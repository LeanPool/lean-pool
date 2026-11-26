/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.FiniteCross
public import LeanPool.GraphMinor.GM11.Ties

/-!
# Growing a forest one line at a time

To prove Graph Minors VII, (3.5) (page 221), we build a forest with given points on `bd(Σ)`, inside
given discs. We start from one point
in each disc. For each other point `y`, we take a line from `y` to the start point of its disc, and
stop at the first point where it hits
what we have built. This file records this process. A state is a finite set `V` of vertices and a
finite set `𝓛` of lines between them (`IsGrown`). The union contains no `O`-arc, because a line
added at one point cannot be part of an `O`-arc. So the drawing we get at the end is a forest
(`exists_grown_forest`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S : Type} [TopologicalSpace S]

/-- The point set of a state. -/
def grownU (V : Set S) (𝓛 : Set (Set S)) : Set S := V ∪ ⋃₀ 𝓛

/-- Two vertices are joined by a line of the state. -/
def GrownAdj (V : Set S) (𝓛 : Set (Set S)) (u v : S) : Prop := ∃ A ∈ 𝓛, A ∩ V = {u, v}

/-- A state of the process. Here `E` is the set of points allowed outside `Q`, the set `Z` must be
met in a finite set, and each line lies in a set of `𝒟`. -/
structure IsGrown (E Q Z : Set S) (𝒟 : Set (Set S)) (V : Set S) (𝓛 : Set (Set S)) : Prop where
  finV : V.Finite
  finL : 𝓛.Finite
  subV : V ⊆ E ∪ Q
  line : ∀ A ∈ 𝓛, ∃ a b, IsLineWithEnds A a b ∧ a ≠ b ∧ A ∩ V = {a, b}
  meet : ∀ A ∈ 𝓛, ∀ A' ∈ 𝓛, A ≠ A' → A ∩ A' ⊆ V
  subL : ∀ A ∈ 𝓛, A ⊆ E ∪ Q
  disc : ∀ A ∈ 𝓛, ∃ D ∈ 𝒟, A ⊆ D
  finZ : (grownU V 𝓛 ∩ Z).Finite
  noO : ∀ F, IsOArc F → F ⊆ grownU V 𝓛 → False

theorem IsGrown.isClosed_U [T2Space S] {E Q Z : Set S} {𝒟 : Set (Set S)} {V : Set S} {𝓛 : Set
  (Set S)} (h : IsGrown E Q Z 𝒟 V 𝓛) :
    IsClosed (grownU V 𝓛) := by
  refine h.finV.isClosed.union (h.finL.isClosed_sUnion fun A hA => ?_)
  obtain ⟨a, b, h1, -⟩ := h.line A hA
  exact h1.isCompact.isClosed

variable [T2Space S]

omit [TopologicalSpace S] [T2Space S] in
theorem reach_mono {r r' : S → S → Prop} (h : ∀ u v, r u v → Relation.ReflTransGen r' u v) {u v :
  S} (hr : Relation.ReflTransGen r u v) :
    Relation.ReflTransGen r' u v := by
  induction hr with
  | refl => exact .refl
  | tail _ h2 ih => exact ih.trans (h _ _ h2)

/-- Making a point of a state into a vertex. -/
theorem IsGrown.subdivide {E Q Z : Set S} {𝒟 : Set (Set S)} {V : Set S} {𝓛 : Set (Set S)}
  (h : IsGrown E Q Z 𝒟 V 𝓛) {p : S} (hp : p ∈ grownU V 𝓛)
    (hpE : p ∈ E ∪ Q) : ∃ V' 𝓛', IsGrown E Q Z 𝒟 V' 𝓛' ∧ p ∈ V' ∧ V ⊆ V' ∧ grownU V' 𝓛'
      = grownU V 𝓛 ∧
      (∀ u v, GrownAdj V 𝓛 u v → Relation.ReflTransGen (GrownAdj V' 𝓛') u v) ∧ (∀ x ∈ V', x ∈ V
        ∨ ∃ u ∈ V, Relation.ReflTransGen (GrownAdj V' 𝓛') x u) := by
  classical
  by_cases hpV : p ∈ V
  · exact ⟨V, 𝓛, h, hpV, subset_rfl, rfl, fun u v huv => .single huv, fun x hx => .inl hx⟩
  obtain ⟨A, hA, hpA⟩ : ∃ A ∈ 𝓛, p ∈ A := by
    rcases hp with hp | ⟨A, hA, hpA⟩
    · exact (hpV hp).elim
    · exact ⟨A, hA, hpA⟩
  obtain ⟨a, b, hl, hab, hcap⟩ := h.line A hA
  have haV : a ∈ V := (hcap ▸ (Or.inl rfl) : a ∈ A ∩ V).2
  have hbV : b ∈ V := (hcap ▸ (Or.inr rfl) : b ∈ A ∩ V).2
  obtain ⟨A₁, A₂, h₁, h₂, hU, hI⟩ := hl.split hpA (fun e => hpV (e ▸ haV)) (fun e => hpV (e ▸ hbV))
  have hsub₁ : A₁ ⊆ A := hU ▸ subset_union_left
  have hsub₂ : A₂ ⊆ A := hU ▸ subset_union_right
  have hoff : ∀ A' ∈ 𝓛, A' ≠ A → p ∉ A' := fun A' hA' hne hp' => hpV (h.meet A hA A' hA' hne.symm
    ⟨hpA, hp'⟩)
  have hcap' : ∀ A' ∈ 𝓛, A' ≠ A → A' ∩ insert p V = A' ∩ V := fun A' hA' hne => by
    rw [inter_insert_of_notMem (hoff A' hA' hne)]
  have hb₁ : b ∉ A₁ := fun h3 => hpV (by
    have : b ∈ A₁ ∩ A₂ := ⟨h3, h₂.right_mem⟩
    rw [hI] at this
    exact (mem_singleton_iff.mp this) ▸ hbV)
  have ha₂ : a ∉ A₂ := fun h3 => hpV (by
    have : a ∈ A₁ ∩ A₂ := ⟨h₁.left_mem, h3⟩
    rw [hI] at this
    exact (mem_singleton_iff.mp this) ▸ haV)
  have hc₁ : A₁ ∩ insert p V = {a, p} := by
    ext z
    constructor
    · rintro ⟨h3, rfl | h4⟩
      · exact .inr rfl
      · have : z ∈ A ∩ V := ⟨hsub₁ h3, h4⟩
        rw [hcap] at this
        rcases this with rfl | h5
        · exact .inl rfl
        · exact (hb₁ (mem_singleton_iff.mp h5 ▸ h3)).elim
    · rintro (rfl | rfl)
      · exact ⟨h₁.left_mem, .inr haV⟩
      · exact ⟨h₁.right_mem, .inl rfl⟩
  have hc₂ : A₂ ∩ insert p V = {p, b} := by
    ext z
    constructor
    · rintro ⟨h3, rfl | h4⟩
      · exact .inl rfl
      · have : z ∈ A ∩ V := ⟨hsub₂ h3, h4⟩
        rw [hcap] at this
        rcases this with rfl | h5
        · exact (ha₂ h3).elim
        · exact .inr h5
    · rintro (rfl | rfl)
      · exact ⟨h₂.left_mem, .inl rfl⟩
      · exact ⟨h₂.right_mem, .inr hbV⟩
  have hne₁ : a ≠ p := fun e => hpV (e ▸ haV)
  have hne₂ : p ≠ b := fun e => hpV (e ▸ hbV)
  have hL' : ∀ B ∈ insert A₁ (insert A₂ (𝓛 \ {A})), B = A₁ ∨ B = A₂ ∨ (B ∈ 𝓛 ∧ B ≠ A) := fun B hB
    => by
    rcases hB with rfl | rfl | ⟨h3, h4⟩
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr ⟨h3, h4⟩)
  have hAU : grownU (insert p V) (insert A₁ (insert A₂ (𝓛 \ {A}))) = grownU V 𝓛 := by
    ext z
    constructor
    · rintro ((rfl | hz) | ⟨B, hB, hz⟩)
      · exact hp
      · exact .inl hz
      · rcases hL' B hB with rfl | rfl | ⟨h3, -⟩
        · exact .inr ⟨A, hA, hsub₁ hz⟩
        · exact .inr ⟨A, hA, hsub₂ hz⟩
        · exact .inr ⟨B, h3, hz⟩
    · rintro (hz | ⟨B, hB, hz⟩)
      · exact .inl (.inr hz)
      · by_cases hBA : B = A
        · subst hBA
          have : z ∈ A₁ ∪ A₂ := hU ▸ hz
          rcases this with h3 | h3
          · exact .inr ⟨A₁, .inl rfl, h3⟩
          · exact .inr ⟨A₂, .inr (.inl rfl), h3⟩
        · exact .inr ⟨B, .inr (.inr ⟨hB, hBA⟩), hz⟩
  have hadj₁ : GrownAdj (insert p V) (insert A₁ (insert A₂ (𝓛 \ {A}))) a p := ⟨A₁, .inl rfl, hc₁⟩
  have hadj₁' : GrownAdj (insert p V) (insert A₁ (insert A₂ (𝓛 \ {A}))) p a
    := ⟨A₁, .inl rfl, by rw [hc₁, pair_comm]⟩
  have hadj₂ : GrownAdj (insert p V) (insert A₁ (insert A₂ (𝓛 \ {A}))) p b := ⟨A₂, .inr
    (.inl rfl), hc₂⟩
  have hadj₂' : GrownAdj (insert p V) (insert A₁ (insert A₂ (𝓛 \ {A}))) b p := ⟨A₂, .inr
    (.inl rfl), by rw [hc₂, pair_comm]⟩
  refine ⟨insert p V, insert A₁ (insert A₂ (𝓛 \ {A})), ⟨h.finV.insert p,
    ((h.finL.subset sdiff_subset).insert _).insert _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    .inl rfl, subset_insert _ _, hAU, ?_, ?_⟩
  · rintro z (rfl | hz)
    · exact hpE
    · exact h.subV hz
  · intro B hB
    rcases hL' B hB with rfl | rfl | ⟨h3, h4⟩
    · exact ⟨a, p, h₁, hne₁, hc₁⟩
    · exact ⟨p, b, h₂, hne₂, hc₂⟩
    · obtain ⟨u, v, h5, h6, h7⟩ := h.line B h3
      exact ⟨u, v, h5, h6, by rw [hcap' B h3 h4, h7]⟩
  · have hAll : ∀ B ∈ insert A₁ (insert A₂ (𝓛 \ {A})), ∀ B' ∈ insert A₁ (insert A₂
      (𝓛 \ {A})), B ≠ A₁ → B' = A₁ ∨ B' = A₂ → B ≠ A₂ → B ∩ B' ⊆ insert p V := by
      intro B hB B' _ hne1 hB' hne2
      rcases hL' B hB with rfl | rfl | ⟨h3, h4⟩
      · exact (hne1 rfl).elim
      · exact (hne2 rfl).elim
      · rintro z ⟨h5, h6⟩
        have h7 : z ∈ A := by
          rcases hB' with rfl | rfl
          · exact hsub₁ h6
          · exact hsub₂ h6
        exact .inr (h.meet B h3 A hA h4 ⟨h5, h7⟩)
    intro B hB B' hB' hne
    rcases hL' B hB with rfl | rfl | ⟨h3, h4⟩ <;> rcases hL' B' hB' with h5 | h5 | ⟨h6, h7⟩
    · exact (hne h5.symm).elim
    · subst h5
      rw [hI]
      exact fun z hz => .inl hz
    · rw [inter_comm]
      exact hAll B' hB' B hB (fun e => (hoff B' h6 h7) (e ▸ h₁.right_mem)) (.inl rfl) (fun e =>
        (hoff B' h6 h7) (e ▸ h₂.left_mem))
    · subst h5
      rw [inter_comm, hI]
      exact fun z hz => .inl hz
    · exact (hne h5.symm).elim
    · rw [inter_comm]
      exact hAll B' hB' B hB (fun e => (hoff B' h6 h7) (e ▸ h₁.right_mem)) (.inr rfl) (fun e =>
        (hoff B' h6 h7) (e ▸ h₂.left_mem))
    · exact hAll B hB B' hB' (fun e => (hoff B h3 h4) (e ▸ h₁.right_mem)) (.inl h5) (fun e =>
        (hoff B h3 h4) (e ▸ h₂.left_mem))
    · exact hAll B hB B' hB' (fun e => (hoff B h3 h4) (e ▸ h₁.right_mem)) (.inr h5) (fun e =>
        (hoff B h3 h4) (e ▸ h₂.left_mem))
    · exact (h.meet B h3 B' h6 hne).trans (subset_insert _ _)
  · intro B hB
    rcases hL' B hB with rfl | rfl | ⟨h3, -⟩
    · exact hsub₁.trans (h.subL A hA)
    · exact hsub₂.trans (h.subL A hA)
    · exact h.subL B h3
  · intro B hB
    rcases hL' B hB with rfl | rfl | ⟨h3, -⟩
    · obtain ⟨D, hD, h4⟩ := h.disc A hA
      exact ⟨D, hD, hsub₁.trans h4⟩
    · obtain ⟨D, hD, h4⟩ := h.disc A hA
      exact ⟨D, hD, hsub₂.trans h4⟩
    · exact h.disc B h3
  · rw [hAU]
    exact h.finZ
  · rw [hAU]
    exact h.noO
  · rintro u v ⟨B, hB, hc⟩
    by_cases hBA : B = A
    · subst hBA
      rw [hcap] at hc
      have huv : (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
        have h3 : u ∈ ({a, b} : Set S) := hc ▸ .inl rfl
        have h4 : v ∈ ({a, b} : Set S) := hc ▸ .inr rfl
        have h5 : a ∈ ({u, v} : Set S) := hc ▸ .inl rfl
        have h6 : b ∈ ({u, v} : Set S) := hc ▸ .inr rfl
        simp only [mem_insert_iff, mem_singleton_iff] at h3 h4 h5 h6
        rcases h3 with rfl | rfl <;> rcases h4 with rfl | rfl <;> simp_all
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (Relation.ReflTransGen.single hadj₁).tail hadj₂
      · exact (Relation.ReflTransGen.single hadj₂').tail hadj₁'
    · exact .single ⟨B, .inr (.inr ⟨hB, hBA⟩), by rw [hcap' B hB hBA, hc]⟩
  · rintro x (rfl | hx)
    · exact .inr ⟨a, haV, .single hadj₁'⟩
    · exact .inl hx

/-- Adding a line at one point of a state. -/
theorem IsGrown.pendant {E Q Z : Set S} {𝒟 : Set (Set S)} {V : Set S} {𝓛 : Set (Set S)}
  (h : IsGrown E Q Z 𝒟 V 𝓛) {y p : S} {P D : Set S} (hl : IsLineWithEnds P y p)
    (hy : y ∉ grownU V 𝓛) (hpV : p ∈ V) (hcap : P ∩ grownU V 𝓛 = {p}) (hPE : P ⊆ insert y E ∪ Q)
      (hD : D ∈ 𝒟) (hPD : P ⊆ D) (hPZ : (P ∩ Z).Finite) :
    IsGrown (insert y E) Q Z 𝒟 (insert y V) (insert P 𝓛) ∧
      (∀ u v, GrownAdj V 𝓛 u v → GrownAdj (insert y V) (insert P 𝓛) u v) ∧ GrownAdj (insert y V)
        (insert P 𝓛) y p := by
  have hyV : y ∉ V := fun e => hy (.inl e)
  have hyL : ∀ A ∈ 𝓛, y ∉ A := fun A hA e => hy (.inr ⟨A, hA, e⟩)
  have hyp : y ≠ p := fun e => hyV (e ▸ hpV)
  have hcapA : ∀ A ∈ 𝓛, A ∩ insert y V = A ∩ V := fun A hA => by rw [inter_insert_of_notMem
    (hyL A hA)]
  have hcapP : P ∩ insert y V = {y, p} := by
    ext z
    constructor
    · rintro ⟨h3, rfl | h4⟩
      · exact .inl rfl
      · have : z ∈ P ∩ grownU V 𝓛 := ⟨h3, .inl h4⟩
        rw [hcap] at this
        exact .inr this
    · rintro (rfl | rfl)
      · exact ⟨hl.left_mem, .inl rfl⟩
      · exact ⟨hl.right_mem, .inr hpV⟩
  have hPA : ∀ A ∈ 𝓛, P ∩ A ⊆ {p} := fun A hA z hz => by
    have : z ∈ P ∩ grownU V 𝓛 := ⟨hz.1, .inr ⟨A, hA, hz.2⟩⟩
    rwa [hcap] at this
  have hE : E ∪ Q ⊆ insert y E ∪ Q := union_subset_union_left _ (subset_insert _ _)
  have hUeq : grownU (insert y V) (insert P 𝓛) = grownU V 𝓛 ∪ P := by
    ext z
    constructor
    · rintro ((rfl | hz) | ⟨B, rfl | hB, hz⟩)
      · exact .inr hl.left_mem
      · exact .inl (.inl hz)
      · exact .inr hz
      · exact .inl (.inr ⟨B, hB, hz⟩)
    · rintro ((hz | ⟨B, hB, hz⟩) | hz)
      · exact .inl (.inr hz)
      · exact .inr ⟨B, .inr hB, hz⟩
      · exact .inr ⟨P, .inl rfl, hz⟩
  refine ⟨⟨h.finV.insert y, h.finL.insert P, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun u v ⟨A, hA,
    hc⟩ => ⟨A, .inr hA, by rw [hcapA A hA, hc]⟩, ⟨P, .inl rfl, hcapP⟩⟩
  · rintro z (rfl | hz)
    · exact .inl (.inl rfl)
    · exact hE (h.subV hz)
  · rintro A (rfl | hA)
    · exact ⟨y, p, hl, hyp, hcapP⟩
    · obtain ⟨a, b, h1, h2, h3⟩ := h.line A hA
      exact ⟨a, b, h1, h2, by rw [hcapA A hA, h3]⟩
  · rintro A (rfl | hA) A' (rfl | hA') hne
    · exact (hne rfl).elim
    · exact (hPA A' hA').trans (fun z hz => .inr (mem_singleton_iff.mp hz ▸ hpV))
    · rw [inter_comm]
      exact (hPA A hA).trans (fun z hz => .inr (mem_singleton_iff.mp hz ▸ hpV))
    · exact (h.meet A hA A' hA' hne).trans (subset_insert _ _)
  · rintro A (rfl | hA)
    · exact hPE
    · exact (h.subL A hA).trans hE
  · rintro A (rfl | hA)
    · exact ⟨D, hD, hPD⟩
    · exact h.disc A hA
  · rw [hUeq, union_inter_distrib_right]
    exact h.finZ.union hPZ
  · intro F hF hsub
    rw [hUeq] at hsub
    have hi : grownU V 𝓛 ∩ P ⊆ {p} := by
      rw [inter_comm, hcap]
    rcases GM11.IsOArc.subset_or_subset hF h.isClosed_U hl.isCompact.isClosed hsub hi with h1 | h1
    · exact h.noO F hF h1
    · exact not_isOArc_of_subset_line (IsLineWithEnds.isLine hl) hF h1

/-- A line from outside a closed set to a point of it has a first point in the set. -/
theorem exists_first_hit {P U : Set S} {y r : S} (hl : IsLineWithEnds P y r) (hU : IsClosed U)
  (hr : r ∈ U) (hy : y ∉ U) :
    ∃ p P', p ∈ U ∧ IsLineWithEnds P' y p ∧ P' ⊆ P ∧ P' ∩ U = {p} := by
  obtain ⟨a, ha, rfl, rfl, rfl⟩ := hl.exists_arc
  have hcl : IsClosed (a ⁻¹' U) := hU.preimage ha.1
  obtain ⟨τ, hτ, hle⟩ := hcl.isCompact.exists_isLeast ⟨1, hr⟩
  have hτ0 : 0 < τ := unitInterval.pos_iff_ne_zero.mpr fun e => hy (e ▸ hτ)
  have hcap : a '' Iic τ ∩ U = {a τ} := by
    ext z
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, h2⟩
      rw [(le_antisymm ht (hle h2) : t = τ)]
      rfl
    · rintro rfl
      exact ⟨⟨τ, le_rfl, rfl⟩, hτ⟩
  by_cases hτ1 : τ < 1
  · exact ⟨a τ, a '' Iic τ, hτ, (split_at ha hτ0 hτ1).1, image_mono (subset_univ _) |>.trans
      (by rw [image_univ]), hcap⟩
  · have h1 : τ = 1 := le_antisymm unitInterval.le_one' (not_lt.mp hτ1)
    subst h1
    refine ⟨a 1, a '' Iic 1, hτ, ?_, ?_, hcap⟩
    · have : a '' Iic 1 = range a := by
        rw [← image_univ]
        congr 1
        ext t
        simp [unitInterval.le_one']
      rw [this]
      exact ha.isLineWithEnds
    · rintro _ ⟨t, -, rfl⟩
      exact ⟨t, rfl⟩

/-- **The forest grows.** Let `R` be a finite set of start points, and suppose that each other point
`y` of a finite set `Y` has a line `P y` to a
point of `R`, inside `Q` apart from its ends and inside a set of `𝒟`, which meets `Z` in a finite
set. Then there is a state with vertices `Y` and
some points of `Q`, in which each vertex is joined to a point of `R`. -/
theorem exists_grown {Y R Q Z : Set S} {𝒟 : Set (Set S)} (hRf : R.Finite) (hYf : Y.Finite)
  (hRY : R ⊆ Y) (hYQ : Disjoint Y Q)
    (hP : ∀ y ∈ Y, y ∉ R → ∃ r ∈ R, ∃ P, ∃ D ∈ 𝒟, IsLineWithEnds P y r ∧ P ⊆ D ∧ P \ {y, r} ⊆ Q ∧
      (P ∩ Z).Finite) :
    ∃ V 𝓛, IsGrown Y Q Z 𝒟 V 𝓛 ∧ Y ⊆ V ∧ ∀ x ∈ V, ∃ r ∈ R, Relation.ReflTransGen (GrownAdj V 𝓛) x r
      := by
  classical
  have key : ∀ I : Finset S, ↑I ⊆ Y \ R → ∃ V 𝓛, IsGrown (R ∪ ↑I) Q Z 𝒟 V 𝓛 ∧ R ∪ ↑I ⊆ V
    ∧ ∀ x ∈ V, ∃ r ∈ R, Relation.ReflTransGen (GrownAdj V 𝓛) x r := by
    intro I
    induction I using Finset.induction_on with
    | empty =>
      intro _
      have h0 : IsGrown R Q Z 𝒟 R ∅ := by
        refine ⟨hRf, finite_empty, subset_union_left, by simp, by simp, by simp, by simp, ?_, ?_⟩
        · refine hRf.subset ?_
          rintro z ⟨h1 | ⟨A, hA, -⟩, -⟩
          · exact h1
          · exact hA.elim
        · intro F hF hsub
          have : F ⊆ R := by
            intro z hz
            rcases hsub hz with h1 | ⟨A, hA, -⟩
            · exact h1
            · exact hA.elim
          exact infinite_of_isOArc hF (hRf.subset this)
      exact ⟨R, ∅, by simpa using h0, by simp, fun x hx => ⟨x, hx, .refl⟩⟩
    | insert y I hyI ih =>
      intro hsub
      have hsub' : (↑I : Set S) ⊆ Y \ R := fun z hz => hsub (Finset.mem_insert_of_mem hz)
      have hyY : y ∈ Y \ R := hsub (Finset.mem_insert_self _ _)
      obtain ⟨V, 𝓛, hG, hV, hR⟩ := ih hsub'
      obtain ⟨r, hr, P, D, hD, hl, hPD, hPQ, hPZ⟩ := hP y hyY.1 hyY.2
      have hrV : r ∈ V := hV (.inl hr)
      have hyQ : y ∉ Q := disjoint_left.mp hYQ hyY.1
      have hyU : y ∉ grownU V 𝓛 := by
        rintro (h1 | ⟨A, hA, h1⟩)
        · rcases h1' : hG.subV h1 with h2 | h2
          · rcases h2 with h2 | h2
            · exact hyY.2 h2
            · exact hyI h2
          · exact hyQ h2
        · rcases hG.subL A hA h1 with h2 | h2
          · rcases h2 with h2 | h2
            · exact hyY.2 h2
            · exact hyI h2
          · exact hyQ h2
      obtain ⟨p, P', hpU, hl', hsubP, hcap⟩ := exists_first_hit hl hG.isClosed_U (.inl hrV) hyU
      have hpE : p ∈ (R ∪ ↑I) ∪ Q := by
        have hpP : p ∈ P := hsubP hl'.right_mem
        by_cases h1 : p ∈ ({y, r} : Set S)
        · rcases h1 with rfl | rfl
          · exact (hyU hpU).elim
          · exact .inl (.inl hr)
        · exact .inr (hPQ ⟨hpP, h1⟩)
      obtain ⟨V₁, 𝓛₁, hG₁, hpV₁, hVV₁, hU₁, hadj₁, hnew₁⟩ := hG.subdivide hpU hpE
      have hyU₁ : y ∉ grownU V₁ 𝓛₁ := hU₁ ▸ hyU
      have hPE : P' ⊆ insert y (R ∪ ↑I) ∪ Q := fun z hz => by
        by_cases h1 : z ∈ ({y, r} : Set S)
        · rcases h1 with rfl | rfl
          · exact .inl (.inl rfl)
          · exact .inl (.inr (.inl hr))
        · exact .inr (hPQ ⟨hsubP hz, h1⟩)
      obtain ⟨hG₂, hadj₂, hyp⟩ := hG₁.pendant hl' hyU₁ hpV₁ (hU₁ ▸ hcap) hPE hD (hsubP.trans hPD)
        (hPZ.subset (inter_subset_inter_left _ hsubP))
      have hmono₁ : ∀ {u v}, Relation.ReflTransGen (GrownAdj V 𝓛) u v → Relation.ReflTransGen
        (GrownAdj V₁ 𝓛₁) u v := reach_mono hadj₁
      have hmono₂ : ∀ {u v}, Relation.ReflTransGen (GrownAdj V₁ 𝓛₁) u v → Relation.ReflTransGen
        (GrownAdj (insert y V₁) (insert P' 𝓛₁)) u v :=
        reach_mono fun u v h => .single (hadj₂ u v h)
      have hreach₁ : ∀ x ∈ V₁, ∃ r ∈ R, Relation.ReflTransGen (GrownAdj V₁ 𝓛₁) x r := fun x hx => by
        rcases hnew₁ x hx with h1 | ⟨u, hu, h1⟩
        · obtain ⟨r', hr', h2⟩ := hR x h1
          exact ⟨r', hr', hmono₁ h2⟩
        · obtain ⟨r', hr', h2⟩ := hR u hu
          exact ⟨r', hr', h1.trans (hmono₁ h2)⟩
      refine ⟨insert y V₁, insert P' 𝓛₁, ?_, ?_, ?_⟩
      · have e : R ∪ ↑(insert y I) = insert y (R ∪ (↑I : Set S)) := by
          ext z
          simp only [mem_union, Finset.mem_coe, Finset.mem_insert, mem_insert_iff]
          tauto
        rw [e]
        exact hG₂
      · rintro z (hz | hz)
        · exact .inr (hVV₁ (hV (.inl hz)))
        · rcases Finset.mem_insert.mp hz with rfl | h1
          · exact .inl rfl
          · exact .inr (hVV₁ (hV (.inr h1)))
      · rintro x (rfl | hx)
        · obtain ⟨r', hr', h2⟩ := hreach₁ p hpV₁
          exact ⟨r', hr', (Relation.ReflTransGen.single hyp).trans (hmono₂ h2)⟩
        · obtain ⟨r', hr', h2⟩ := hreach₁ x hx
          exact ⟨r', hr', hmono₂ h2⟩
  obtain ⟨V, 𝓛, h1, h2, h3⟩ := key (hYf.subset (sdiff_subset (t := R))).toFinset
    (by rw [Finite.coe_toFinset])
  have e : R ∪ ↑(hYf.subset (sdiff_subset (t := R))).toFinset = Y := by
    rw [Finite.coe_toFinset]
    ext z
    constructor
    · rintro (h | h)
      · exact hRY h
      · exact h.1
    · intro h
      by_cases h' : z ∈ R
      · exact .inl h'
      · exact .inr ⟨h, h'⟩
  rw [e] at h1 h2
  exact ⟨V, 𝓛, h1, h2, h3⟩

/-- A drawing whose point set contains no `O`-arc is a forest. -/
theorem isGraphForest_of_noOArc {H : Drawing S} (h : ∀ F, IsOArc F → F ⊆ H.U
  → False) : IsGraphForest H.toGraph := by
  intro u W hW
  by_contra hne
  have hC := isCircuit_walkDrawing H hW (Nat.pos_of_ne_zero hne)
  exact h _ (IsCircuit.isOArc_U hC) (walkDrawing_isSubdrawing H W).U_subset

end GraphMinor.GM07
