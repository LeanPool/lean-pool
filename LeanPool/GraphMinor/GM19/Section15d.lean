/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section12a
public import LeanPool.GraphMinor.GM19.Section11g

/-!
# Graph Minors XIX, (15.2): the choice of the edges

This is step (1) of the proof of (15.2). If the third and fourth outcomes of (15.2) fail, then each
edge `e` of `Γ₀` has an image `β(e)` in `Γ`, of the same size and with a larger colour, and the
images are far apart. The result used later is `exists_edgeMap`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}

namespace TangleDatum

/-- What step (1) of the proof of (15.2) says about a long side: the edges `f` of `Γ₀` along the
side, in order, have images `g` in `Γ`, in order. -/
structure IsSideMap (D : TangleDatum cap χ) (P₀ : ColouredPainting χ) (n : ℕ) (b : Set S → Set S)
  (side : Set S) (m : ℕ) (f g : Fin m → Set S) (c : Set S) (r : Shat)
    (u₀ u₁ u₀' u₁' : S) : Prop where
  pole : r ∈ D.rad.poles
  cuff : c ∈ cuffs S
  pole_disc : r ∈ cap.cuffDisc c
  side_cuff : side ⊆ c
  order₀ : BordersInOrder χ P₀.Γ side c f u₀ u₁
  all₀ : ∀ e ∈ P₀.Γ.E, e ⊆ side → ∃ i, f i = e
  order : BordersInOrder χ D.P.Γ side c g u₀' u₁'
  map : ∀ i, b (f i) = g i
  le : ∀ i, (χ.ΩS side).le (P₀.φ (f i)) (D.P.φ (g i))
  far : ∀ i j, i < j → n / 2 < D.borderEdgeDist r (g i) (g j)
  far_short : ∀ i, ∀ s ∈ χ.Φ.shortSides, s ⊆ c → n / 2 < D.borderEdgeDist r (g i) s

/-- What step (1) of the proof of (15.2) gives. -/
structure IsEdgeMap (D : TangleDatum cap χ) (P₀ : ColouredPainting χ) (n : ℕ) (b : Set S
  → Set S) : Prop where
  mem : ∀ e ∈ P₀.Γ.E, b e ∈ D.P.Γ.E
  injOn : InjOn b P₀.Γ.E
  short : ∀ s ∈ χ.Φ.shortSides, b s = s
  size : ∀ e ∈ P₀.Γ.E, (tilde (b e)).ncard = (tilde e).ncard
  side : ∀ side ∈ χ.Φ.longSides, ∃ m f g c r u₀ u₁ u₀' u₁', D.IsSideMap P₀ n b side m f g c r u₀ u₁
    u₀' u₁'
  internal : ∀ e ∈ P₀.Γ.E, Painting.IsInternal e → Painting.IsInternal (b e)
  internal_le : ∀ e ∈ P₀.Γ.E, Painting.IsInternal e → sizeLE χ (tilde e).ncard (P₀.φ e) (D.P.φ
    (b e))
  pole_far : ∀ e ∈ P₀.Γ.E, Painting.IsInternal e → ∀ r ∈ D.rad.poles, n < D.edgeVertDist (b e) r
  far : ∀ e ∈ P₀.Γ.E, Painting.IsInternal e → ∀ e' ∈ P₀.Γ.E, Painting.IsInternal e' → e ≠ e'
    → n / 2 < D.edgeDist (b e) (b e')

variable {D : TangleDatum cap χ} {P₀ : ColouredPainting χ}

/-- **The internal edges.** Given images of the edges of a set `𝓘`, a new edge has `|E(Γ₀)|`
candidates far apart. If each of them were within `½n` of an old image, then two would be within
`½n` of one
image, and so within `n` of each other. -/
theorem exists_internal_images {n : ℕ} (hn : Even n) (hrep : 4 ≤ D.rep)
    (h4 : ∀ f ∈ P₀.Γ.E, Painting.IsInternal f → ¬ D.NoInternalMatch P₀.Γ.E.ncard n (tilde f).ncard
      (P₀.φ f)) (𝓘 : Finset (Set S)) (h𝓘 : ∀ e ∈ 𝓘, e ∈ P₀.Γ.E ∧ Painting.IsInternal e) :
    ∃ b : Set S → Set S, (∀ e ∈ 𝓘, b e ∈ D.P.Γ.E ∧ Painting.IsInternal (b e) ∧ (tilde (b e)).ncard
      = (tilde e).ncard ∧ sizeLE χ (tilde e).ncard (P₀.φ e) (D.P.φ (b e)) ∧
      ∀ r ∈ D.rad.poles, n < D.edgeVertDist (b e) r) ∧ ∀ e ∈ 𝓘, ∀ e' ∈ 𝓘, e ≠ e'
        → n / 2 < D.edgeDist (b e) (b e') := by
  classical
  induction 𝓘 using Finset.induction_on with
  | empty => exact ⟨id, by simp, by simp⟩
  | insert f₀ 𝓘 hf₀ ih =>
    obtain ⟨b, hb₁, hb₂⟩ := ih fun e he ↦ h𝓘 e (Finset.mem_insert_of_mem he)
    obtain ⟨hf₀E, hf₀I⟩ := h𝓘 f₀ (Finset.mem_insert_self _ _)
    have hn' := h4 f₀ hf₀E hf₀I
    unfold NoInternalMatch at hn'
    rw [not_not] at hn'
    obtain ⟨c, hc, hfar, hpole⟩ := hn'
    have hcard : 𝓘.card < P₀.Γ.E.ncard := by
      have hsub : ((insert f₀ 𝓘 : Finset (Set S)) : Set (Set S)) ⊆ P₀.Γ.E := fun e he ↦ (h𝓘 e
        (Finset.mem_coe.1 he)).1
      have := ncard_le_ncard hsub P₀.Γ.finite_edges
      rw [ncard_coe_finset, Finset.card_insert_of_notMem hf₀] at this
      omega
    have hex : ∃ j, ∀ e ∈ 𝓘, n / 2 < D.edgeDist (b e) (c j) := by
      by_contra hno
      push Not at hno
      choose t ht ht' using hno
      have hne : ¬ Function.Injective (fun j ↦ (⟨t j, ht j⟩ : {x // x ∈ 𝓘})) := fun hinj ↦ by
        have := Fintype.card_le_of_injective _ hinj
        simp at this
        omega
      rw [Function.Injective] at hne
      push Not at hne
      obtain ⟨j, j', he, hjj⟩ := hne
      have he' : t j = t j' := congrArg Subtype.val he
      have htj := hb₁ (t j) (ht j)
      have hat : cap.emb '' b (t j) ∈ D.P.Γ.atoms cap := Or.inl (Or.inr ⟨_, htj.1, rfl⟩)
      have htri := D.dist_triangle hrep (a := cap.emb '' c j) (b := cap.emb '' b (t j)) (c
        := cap.emb '' c j') hat
      have h₁ : D.dist (cap.emb '' c j) (cap.emb '' b (t j)) ≤ n / 2 := by
        rw [D.dist_comm]
        exact ht' j
      have h₂ : D.dist (cap.emb '' b (t j)) (cap.emb '' c j') ≤ n / 2 := by
        rw [he']
        exact ht' j'
      obtain ⟨k, hk⟩ := hn
      rcases lt_or_gt_of_ne (fun h ↦ hjj (Fin.ext h) : j.1 ≠ j'.1) with hlt | hlt
      · have := hfar j j' hlt
        change n < D.dist _ _ at this
        omega
      · have := hfar j' j hlt
        rw [edgeDist, D.dist_comm] at this
        omega
    obtain ⟨j, hj⟩ := hex
    obtain ⟨hc₁, hc₂, hc₃, hc₄⟩ := hc j
    refine ⟨Function.update b f₀ (c j), fun e he ↦ ?_, fun e he e' he' hne ↦ ?_⟩
    · rcases Finset.mem_insert.1 he with rfl | he
      · rw [Function.update_self]
        exact ⟨hc₁, hc₂, hc₃, hc₄, hpole j⟩
      · have hne : e ≠ f₀ := fun h ↦ hf₀ (h ▸ he)
        rw [Function.update_of_ne hne]
        exact hb₁ e he
    · rcases Finset.mem_insert.1 he with rfl | he₁
      · rcases Finset.mem_insert.1 he' with rfl | he₂
        · exact absurd rfl hne
        · have hne' : e' ≠ e := hne.symm
          rw [Function.update_self, Function.update_of_ne hne', edgeDist, D.dist_comm]
          exact hj e' he₂
      · have hne₁ : e ≠ f₀ := fun h ↦ hf₀ (h ▸ he₁)
        rcases Finset.mem_insert.1 he' with rfl | he₂
        · rw [Function.update_of_ne hne₁, Function.update_self]
          exact hj e he₁
        · have hne₂ : e' ≠ f₀ := fun h ↦ hf₀ (h ▸ he₂)
          rw [Function.update_of_ne hne₁, Function.update_of_ne hne₂]
          exact hb₂ e he₁ e' he₂ hne

omit [T2Space S] [T2Space Shat] in
/-- A long side has the data of `IsSideMap` when the third outcome fails. -/
theorem exists_sideMap {n : ℕ} {side : Set S} (hside : side ∈ χ.Φ.longSides) {ω : List β}
  (hl : IsBorderLabels P₀ side ω) (h3 : ¬ D.NoSideMatch side (n / 2) ω) :
    ∃ (m : ℕ) (f g : Fin m → Set S) (c : Set S) (r : Shat) (u₀ u₁ u₀' u₁' : S), BordersInOrder χ
      P₀.Γ side c f u₀ u₁ ∧ BordersInOrder χ D.P.Γ side c g u₀' u₁' ∧ ∀ b : Set S → Set S, (∀ i, b
        (f i) = g i) → D.IsSideMap P₀ n b side m f g c r u₀ u₁ u₀' u₁' := by
  obtain ⟨-, -, c₀, f, u₀, u₁, hc₀, hs₀, hord₀, hall, hω⟩ := hl
  unfold NoSideMatch at h3
  push Not at h3
  obtain ⟨r, hr, c, hc, hrd, hsc, g, u₀', u₁', hord, hle, hfar, hshort⟩ := h3
  obtain ⟨x, hx⟩ : side.Nonempty := hside.1.1
  obtain rfl : c₀ = c := cuffs_eq_of_mem hc₀ hc (hs₀ hx) (hsc hx)
  exact ⟨_, f, g, c₀, r, u₀, u₁, u₀', u₁', hord₀, hord, fun b hb ↦ ⟨hr, hc, hrd, hsc, hord₀, hall,
    hord, hb, fun i ↦ hω i ▸ hle i, fun i j hij ↦ hfar i j hij, fun i s hs hsub ↦ hshort i s hs
      hsub⟩⟩

omit [T2Space S] in
/-- An edge inside a short side is that side. -/
theorem eq_short_of_subset {Γ : Painting S} (hfit : Γ.Fits χ.Φ) {e s : Set S} (he : e ∈ Γ.E)
  (hs : s ∈ χ.Φ.shortSides) (hsub : e ⊆ s) : e = s := by
  obtain ⟨x, hx⟩ : e.Nonempty := he.1
  exact GM11.arcComponent_eq he (hfit.short_sides hs) hx (hsub hx)

/-- **Step (1) of the proof of (15.2).** -/
theorem exists_edgeMap {n : ℕ} (hn : Even n) (hrep : 4 ≤ D.rep) {ω : Set S → List β}
  (hl : ∀ side ∈ χ.Φ.longSides, IsBorderLabels P₀ side (ω side))
    (h3 : ∀ side ∈ χ.Φ.longSides, ¬ D.NoSideMatch side (n / 2) (ω side))
    (h4 : ∀ f ∈ P₀.Γ.E, Painting.IsInternal f → ¬ D.NoInternalMatch P₀.Γ.E.ncard n (tilde f).ncard
      (P₀.φ f)) : ∃ b, D.IsEdgeMap P₀ n b := by
  classical
  have hfin : {e ∈ P₀.Γ.E | Painting.IsInternal e}.Finite := P₀.Γ.finite_edges.subset fun _ h ↦ h.1
  obtain ⟨bI, hI₁, hI₂⟩ := exists_internal_images (D := D) hn hrep h4 hfin.toFinset fun e he ↦
    hfin.mem_toFinset.1 he
  have hI₁' : ∀ e ∈ P₀.Γ.E, Painting.IsInternal e → _ := fun e he hi ↦ hI₁ e
    (hfin.mem_toFinset.2 ⟨he, hi⟩)
  have hsm : ∀ side : {s // s ∈ χ.Φ.longSides}, _ := fun side ↦ exists_sideMap (D := D) (n
    := n) side.2 (hl side.1 side.2) (h3 side.1 side.2)
  choose m f g c r u₀ u₁ u₀' u₁' hO₀ hO hSM using hsm
  have hfE : ∀ s i, f s i ∈ P₀.Γ.E := fun s i ↦ ((hO₀ s).2.2.2.1 i).1
  have hfs : ∀ s i, f s i ⊆ s.1 := fun s i ↦ ((hO₀ s).2.2.2.1 i).2
  have hgE : ∀ s i, g s i ∈ D.P.Γ.E := fun s i ↦ ((hO s).2.2.2.1 i).1
  have hgs : ∀ s i, g s i ⊆ s.1 := fun s i ↦ ((hO s).2.2.2.1 i).2
  have hside : ∀ {Γ : Painting S} {e} {s s' : Set S}, e ∈ Γ.E → s ∈ χ.Φ.sides → s' ∈ χ.Φ.sides
    → e ⊆ s → e ⊆ s' → s = s' := fun {Γ e s s'} he hs hs' h₁ h₂ ↦ by
    obtain ⟨x, hx⟩ : e.Nonempty := he.1
    exact GM11.arcComponent_eq hs hs' (h₁ hx) (h₂ hx)
  have huniq : ∀ {p q : Σ s : {s // s ∈ χ.Φ.longSides}, Fin (m s)}, f p.1 p.2 = f q.1 q.2 → p = q
    := by
    rintro ⟨s, i⟩ ⟨s', i'⟩ he
    have h₁ : s = s' := Subtype.ext (hside (hfE s i) s.2.1 s'.2.1 (hfs s i) (he ▸ hfs s' i'))
    subst h₁
    obtain rfl : i = i' := (hO₀ s).2.2.1 he
    rfl
  have hbd : ∀ {Γ : Painting S} {e s : Set S}, e ∈ Γ.E → s ∈ χ.Φ.sides → e ⊆ s
    → ¬ Painting.IsInternal e := fun {Γ e s} he hs hsub hi ↦ by
    obtain ⟨x, hx⟩ : e.Nonempty := he.1
    exact disjoint_left.1 hi hx (hs.2.1 (hsub hx)).1
  let b : Set S → Set S := fun e ↦ if Painting.IsInternal e then bI e else if h : ∃ p : Σ s : {s //
    s ∈ χ.Φ.longSides}, Fin (m s), f p.1 p.2 = e then g h.choose.1 h.choose.2 else e
  have hbI : ∀ {e}, Painting.IsInternal e → b e = bI e := fun {e} h ↦ ite_eq_left h
  have hbf : ∀ s i, b (f s i) = g s i := fun s i ↦ by
    have hn : ¬ Painting.IsInternal (f s i) := hbd (hfE s i) s.2.1 (hfs s i)
    have hex : ∃ p : Σ s : {s // s ∈ χ.Φ.longSides}, Fin (m s), f p.1 p.2 = f s i := ⟨⟨s, i⟩, rfl⟩
    simp only [b, ite_eq_right hn, dite_eq_left hex]
    have he := huniq (p := hex.choose) (q := ⟨s, i⟩) hex.choose_spec
    rw [he]
  have hbs : ∀ s ∈ χ.Φ.shortSides, b s = s := fun s hs ↦ by
    have hsE := P₀.fits.short_sides hs
    have hn : ¬ Painting.IsInternal s := hbd hsE hs.1 Subset.rfl
    have hex : ¬ ∃ p : Σ s : {s // s ∈ χ.Φ.longSides}, Fin (m s), f p.1 p.2 = s := by
      rintro ⟨⟨s', i⟩, he⟩
      have := hside hsE hs.1 s'.2.1 Subset.rfl (he ▸ hfs s' i)
      exact hs.2 (this ▸ s'.2.2)
    simp only [b, ite_eq_right hn, dite_eq_right hex]
  have hcases : ∀ e ∈ P₀.Γ.E, Painting.IsInternal e ∨ e ∈ χ.Φ.shortSides ∨ ∃ s i, f s i = e
    := fun e he ↦ by
    by_cases hi : Painting.IsInternal e
    · exact Or.inl hi
    · have hb : Painting.IsBorder e := by
        rw [Painting.IsBorder, ← not_disjoint_iff_nonempty_inter]
        exact hi
      obtain ⟨s, hs, hs₁, hs₂⟩ := Painting.exists_side P₀.fits he hb
      by_cases hl' : s ∈ χ.Φ.longSides
      · obtain ⟨i, rfl⟩ := (hSM ⟨s, hl'⟩ b (hbf _)).all₀ e he hs₂
        exact Or.inr (Or.inr ⟨_, i, rfl⟩)
      · have hss : s ∈ χ.Φ.shortSides := ⟨hs, fun h ↦ hl' ⟨hs, h⟩⟩
        exact Or.inr (Or.inl ((eq_short_of_subset P₀.fits he hss hs₂) ▸ hss))
  have hbInt : ∀ {e}, e ∈ P₀.Γ.E → Painting.IsInternal e → _ := fun {e} he hi ↦ hI₁' e he hi
  have hsideD : ∀ {e}, e ∈ χ.Φ.shortSides → e ∈ D.P.Γ.E := fun h ↦ D.P.fits.short_sides h
  refine ⟨b, ⟨fun e he ↦ ?_, ?_, hbs, fun e he ↦ ?_, fun side hside' ↦ ?_, fun e he hi ↦ ?_,
    fun e he hi ↦ ?_, fun e he hi r' hr ↦ ?_, fun e he hi e' he' hi' hne ↦ ?_⟩⟩
  · rcases hcases e he with h | h | ⟨s, i, rfl⟩
    · rw [hbI h]
      exact (hbInt he h).1
    · rw [hbs e h]
      exact hsideD h
    · rw [hbf]
      exact hgE s i
  · have key : ∀ e ∈ P₀.Γ.E, ∀ e' ∈ P₀.Γ.E, Painting.IsInternal e → ¬ Painting.IsInternal e'
      → b e ≠ b e' := by
      intro e he e' he' hi hi' heq
      have h₁ := (hbInt he hi).2.1
      rw [← hbI hi, heq] at h₁
      rcases hcases e' he' with h | h | ⟨s, i, rfl⟩
      · exact hi' h
      · rw [hbs e' h] at h₁
        exact hbd (hsideD h) h.1 Subset.rfl h₁
      · rw [hbf] at h₁
        exact hbd (hgE s i) s.2.1 (hgs s i) h₁
    intro e he e' he' heq
    by_cases hi : Painting.IsInternal e
    · by_cases hi' : Painting.IsInternal e'
      · by_contra hne
        have := hI₂ e (hfin.mem_toFinset.2 ⟨he, hi⟩) e' (hfin.mem_toFinset.2 ⟨he', hi'⟩) hne
        rw [← hbI hi, ← hbI hi', heq, edgeDist, D.dist_self] at this
        omega
      · exact absurd heq (key e he e' he' hi hi')
    · by_cases hi' : Painting.IsInternal e'
      · exact absurd heq.symm (key e' he' e he hi' hi)
      · rcases hcases e he with h | h | ⟨s, i, rfl⟩
        · exact absurd h hi
        · rcases hcases e' he' with h' | h' | ⟨s', i', rfl⟩
          · exact absurd h' hi'
          · rw [hbs e h, hbs e' h'] at heq
            exact heq
          · exfalso
            rw [hbs e h, hbf] at heq
            have := hside (hsideD h) h.1 s'.2.1 Subset.rfl (heq ▸ hgs s' i')
            exact h.2 (this ▸ s'.2.2)
        · rcases hcases e' he' with h' | h' | ⟨s', i', rfl⟩
          · exact absurd h' hi'
          · exfalso
            rw [hbf, hbs e' h'] at heq
            have := hside (hsideD h') h'.1 s.2.1 Subset.rfl (heq ▸ hgs s i)
            exact h'.2 (this ▸ s.2.2)
          · rw [hbf, hbf] at heq
            have h₁ : s = s' := Subtype.ext (hside (hgE s i) s.2.1 s'.2.1 (hgs s i)
              (heq ▸ hgs s' i'))
            subst h₁
            rw [(hO s).2.2.1 heq]
  · have htwo : ∀ {Γ : Painting S} {e s : Set S}, e ∈ Γ.E → s ∈ χ.Φ.sides → e ⊆ s → (tilde e).ncard
      = 2 := fun {Γ e s} he hs hsub ↦ by
      obtain ⟨x, hx⟩ : e.Nonempty := he.1
      exact (Γ.border_edge e he ⟨x, hx, (hs.2.1 (hsub hx)).1⟩).1
    rcases hcases e he with h | h | ⟨s, i, rfl⟩
    · rw [hbI h]
      exact (hbInt he h).2.2.1
    · rw [hbs e h]
    · rw [hbf, htwo (hgE s i) s.2.1 (hgs s i), htwo he s.2.1 (hfs s i)]
  · exact ⟨_, _, _, _, _, _, _, _, _, hSM ⟨side, hside'⟩ b (hbf _)⟩
  · rw [hbI hi]
    exact (hbInt he hi).2.1
  · rw [hbI hi]
    exact (hbInt he hi).2.2.2.1
  · rw [hbI hi]
    exact (hbInt he hi).2.2.2.2 r' hr
  · rw [hbI hi, hbI hi']
    exact hI₂ e (hfin.mem_toFinset.2 ⟨he, hi⟩) e' (hfin.mem_toFinset.2 ⟨he', hi'⟩) hne

end TangleDatum

end GraphMinor.GM19
