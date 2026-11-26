/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Defs2
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Order.OrderIsoNat

/-!
# Graph Minors XIX, (4.2)

A bad colour scheme gives an orientedly bad one on the same surface. We reverse the last two terms
of
the march of each disc edge whose cyclic order disagrees with a chosen orientation, and we record
this
in a second coordinate of the label (`±1` in the paper, `Bool` here). All the new labels live on
`α × Bool`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology GraphMinor.Surface

universe u w

variable {S : Type u} [TopologicalSpace S] {α : Type w}

/-! ### The circle -/

/-- Each point of the circle other than `1` has an angle strictly between `0` and `2π`. -/
theorem exists_angle {z : Circle} (hz : z ≠ 1) :
    ∃ s : ℝ, 0 < s ∧ s < 2 * Real.pi ∧ z = Circle.exp s :=
  CircleOrder.exists_angle hz

/-- Three distinct points of the circle occur in one of the two cyclic orders. -/
theorem circleCyclic_or {a b c : Circle} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    CircleCyclic a b c ∨ CircleCyclic a c b :=
  CircleOrder.circleCyclic_or hab hac hbc

/-- Three distinct boundary points of a closed disc occur in one of the two cyclic orders of an
orientation. -/
theorem SurfaceOrientation.pos_or (ω : SurfaceOrientation S) {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {a b c : S} (ha : a ∈ discBd Δ) (hb : b ∈ discBd Δ) (hc : c ∈ discBd Δ) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : ω.pos Δ a b c ∨ ω.pos Δ a c b := by
  obtain ⟨φ, -, hinj, hrange, hφ⟩ := ω.isDirection Δ hΔ
  rw [← hrange] at ha hb hc
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  obtain ⟨c, rfl⟩ := hc
  have hab' : a ≠ b := fun h ↦ hab (by rw [h])
  have hac' : a ≠ c := fun h ↦ hac (by rw [h])
  have hbc' : b ≠ c := fun h ↦ hbc (by rw [h])
  rcases circleCyclic_or hab' hac' hbc' with h | h
  · exact Or.inl ((hφ a b c hab' hbc' hac').2 h)
  · exact Or.inr ((hφ a c b hac' hbc'.symm hab').2 h)

/-! ### Quasi-orders on `α × Bool` -/

namespace QuasiOrder

/-- The copy of `Ω` with second coordinate `true`. -/
def liftTrue (Ω : QuasiOrder α) : QuasiOrder (α × Bool) where
  E := {p | p.1 ∈ Ω.E ∧ p.2 = true}
  le x y := Ω.le x.1 y.1 ∧ x.2 = y.2
  refl _x hx := ⟨Ω.refl _ hx.1, rfl⟩
  trans _x hx _y hy _z hz h₁ h₂ :=
    ⟨Ω.trans _ hx.1 _ hy.1 _ hz.1 h₁.1 h₂.1, h₁.2.trans h₂.2⟩

/-- The product `Ω × R`, where `R` has two elements, ordered by equality. -/
def prodBool (Ω : QuasiOrder α) : QuasiOrder (α × Bool) where
  E := {p | p.1 ∈ Ω.E}
  le x y := Ω.le x.1 y.1 ∧ x.2 = y.2
  refl _x hx := ⟨Ω.refl _ hx, rfl⟩
  trans _x hx _y hy _z hz h₁ h₂ := ⟨Ω.trans _ hx _ hy _ hz h₁.1 h₂.1, h₁.2.trans h₂.2⟩

theorem liftTrue_isWQO {Ω : QuasiOrder α} (h : Ω.IsWQO) : Ω.liftTrue.IsWQO := fun f hf ↦ by
  obtain ⟨i, j, hij, hle⟩ := h (fun n ↦ (f n).1) fun n ↦ (hf n).1
  exact ⟨i, j, hij, hle, (hf i).2.trans (hf j).2.symm⟩

theorem prodBool_isWQO {Ω : QuasiOrder α} (h : Ω.IsWQO) : Ω.prodBool.IsWQO := fun f hf ↦ by
  classical
  have key : ∀ b : Bool, {n | (f n).2 = b}.Infinite → ∃ i j, i < j ∧ Ω.prodBool.le (f i) (f j) := by
    intro b hb
    have : Infinite {n | (f n).2 = b} := hb.to_subtype
    let g := Nat.orderEmbeddingOfSet {n | (f n).2 = b}
    have hg : ∀ n, (f (g n)).2 = b := fun n ↦ by
      have := mem_range_self (f := g) n
      rwa [Nat.orderEmbeddingOfSet_range] at this
    obtain ⟨i, j, hij, hle⟩ := h (fun n ↦ (f (g n)).1) fun n ↦ hf (g n)
    exact ⟨g i, g j, g.strictMono hij, hle, (hg i).trans (hg j).symm⟩
  by_cases hT : {n | (f n).2 = true}.Infinite
  · exact key true hT
  · refine key false ?_
    intro hF
    have huniv : ({n | (f n).2 = true} ∪ {n | (f n).2 = false}) = univ := by
      ext n
      cases hb : (f n).2 <;> simp [hb]
    exact Set.infinite_univ (huniv ▸ (Set.not_infinite.1 hT).union hF)

end QuasiOrder

/-- The colour scheme `χ'` of (4.2): `Ω_{χ'}(3) = Ω_χ(3) × R`, and the other quasi-orders are copied
to `α × Bool`. -/
def ColourScheme.orient (χ : ColourScheme S α) : ColourScheme S (α × Bool) where
  isSurface := χ.isSurface
  connected := χ.connected
  Φ := χ.Φ
  Ω2 := χ.Ω2.liftTrue
  Ω3 := χ.Ω3.prodBool
  ΩS s := (χ.ΩS s).liftTrue
  shortElem s := (χ.shortElem s, true)
  isWQO_2 := QuasiOrder.liftTrue_isWQO χ.isWQO_2
  isWQO_3 := QuasiOrder.prodBool_isWQO χ.isWQO_3
  isWQO_S s hs := QuasiOrder.liftTrue_isWQO (χ.isWQO_S s hs)
  short_singleton s hs := by
    ext ⟨x, b⟩
    have := χ.short_singleton s hs
    simp only [QuasiOrder.liftTrue, mem_ofPred_eq, mem_singleton_iff, Prod.mk.injEq, this]

/-! ### Reversing marches -/

/-- The march `[a, b, c]` becomes `[a, c, b]`. Other marches stay as they are. -/
def swapTail : List S → List S
  | [a, b, c] => [a, c, b]
  | l => l

omit [TopologicalSpace S] in
theorem swapTail_perm (l : List S) : (swapTail l).Perm l := by
  match l with
  | [] => exact List.Perm.refl _
  | [_] => exact List.Perm.refl _
  | [_, _] => exact List.Perm.refl _
  | [_, _, _] => exact List.Perm.cons _ (List.Perm.swap _ _ _)
  | _ :: _ :: _ :: _ :: _ => exact List.Perm.refl _

omit [TopologicalSpace S] in
theorem swapTail_head (l : List S) : (swapTail l).head? = l.head? := by
  match l with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: _ :: _ :: _ :: _ => rfl

open Classical in
/-- `Γ` with the march of each edge in `B` reversed by `swapTail`. -/
noncomputable def Painting.swapOn (Γ : Painting S) (B : Set S → Prop) : Painting S where
  U := Γ.U
  V := Γ.V
  γ e := if B e then swapTail (Γ.γ e) else Γ.γ e
  isClosed_U := Γ.isClosed_U
  V_subset := Γ.V_subset
  finite_V := Γ.finite_V
  bd_subset := Γ.bd_subset
  finite_edges := Γ.finite_edges
  edge_shape := Γ.edge_shape
  γ_nodup e he := by
    split_ifs
    · exact (swapTail_perm _).nodup_iff.2 (Γ.γ_nodup e he)
    · exact Γ.γ_nodup e he
  γ_set e he := by
    rw [← Γ.γ_set e he]
    split_ifs
    · ext v
      exact (swapTail_perm _).mem_iff
    · rfl
  border_edge := Γ.border_edge

/-- The length of `γ(e)` is the number of ends of `e`. -/
theorem Painting.length_γ (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) :
    (Γ.γ e).length = (tilde e).ncard := by
  classical
  rw [← Γ.γ_set e he]
  have : {v | v ∈ Γ.γ e} = ((Γ.γ e).toFinset : Set S) := by
    ext v
    simp
  rw [this, ncard_coe_finset, List.toFinset_card_of_nodup (Γ.γ_nodup e he)]

/-- A march of length three, written out. -/
theorem Painting.exists_three (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E)
    (h3 : (tilde e).ncard = 3) : ∃ a b c, Γ.γ e = [a, b, c] := by
  have hlen := Γ.length_γ he
  rw [h3] at hlen
  match hl : Γ.γ e, hlen with
  | [a, b, c], _ => exact ⟨a, b, c, rfl⟩

/-- An edge of a coloured painting that borders a side has two ends. -/
theorem Painting.ncard_of_border (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E)
    (hb : Painting.IsBorder e) : (tilde e).ncard = 2 :=
  (Γ.border_edge e he hb).1

/-! ### The new paintings -/

open Classical in
/-- The `χ'`-coloured painting of (4.2), where `B` is the set of disc edges to be reversed. -/
noncomputable def ColouredPainting.orient {χ : ColourScheme S α} (P : ColouredPainting χ)
    (B : Set S → Prop) (hB : ∀ e, B e → (tilde e).ncard = 3) : ColouredPainting χ.orient where
  Γ := P.Γ.swapOn B
  φ e := (P.φ e, decide (¬ B e))
  fits :=
    { V_subset := P.fits.V_subset
      short_sides := P.fits.short_sides
      border_dir := fun e he hb s hs hes ↦ by
        have h := P.fits.border_dir e he hb s hs hes
        have hnB : ¬ B e := fun h' ↦ by
          have h2 := P.Γ.ncard_of_border he hb
          have h3 := hB e h'
          omega
        have hγ : (P.Γ.swapOn B).γ e = P.Γ.γ e := by simp [Painting.swapOn, hnB]
        change DirAgrees s (χ.Φ.γ s) e _
        rw [hγ]
        exact h
      internally_three_connected := P.fits.internally_three_connected
      size_three_region := P.fits.size_three_region }
  internal_2_mem e he hi h2 := by
    have hnB : ¬ B e := fun h' ↦ by
      have h3 := hB e h'
      omega
    exact ⟨P.internal_2_mem e he hi h2, by simpa using hnB⟩
  internal_3_mem e he hi h3 := P.internal_3_mem e he hi h3
  border_mem e he s hs hes := by
    have hnB : ¬ B e := fun h' ↦ by
      have h2 := P.Γ.ncard_of_border he hes.1
      have h3 := hB e h'
      omega
    exact ⟨P.border_mem e he s hs hes, by simpa using hnB⟩

/-- A linear inflation of the new paintings is a linear inflation of the old ones. This is the only
step of (4.2) that the paper writes out. -/
theorem IsColouredLinearInflation.of_orient {χ : ColourScheme S α} {P P' : ColouredPainting χ}
    {B B' : Set S → Prop} {hB : ∀ e, B e → (tilde e).ncard = 3}
    {hB' : ∀ e, B' e → (tilde e).ncard = 3} {σv : S → Set S} {σe : Set S → Set S}
    (h : IsColouredLinearInflation χ.orient (P.orient B hB) (P'.orient B' hB') σv σe) :
    IsColouredLinearInflation χ P P' σv σe := by
  classical
  have hinf := h.isInflation
  have hsize := hinf.edge_size
  have hE : ∀ e ∈ P.Γ.E, e ∈ (P.orient B hB).Γ.E := fun _ he ↦ he
  have hsame : ∀ e ∈ P.Γ.E, (B e ↔ B' (σe e)) := by
    intro e he
    by_cases h3 : (tilde e).ncard = 3
    · have hint : Painting.IsInternal e := by
        by_contra hn
        have hb : Painting.IsBorder e := by
          rw [Painting.IsBorder, Set.nonempty_iff_ne_empty]
          intro hem
          exact hn (Set.disjoint_iff_inter_eq_empty.2 hem)
        have := P.Γ.ncard_of_border he hb
        omega
      have := (h.le_internal_3 e he hint h3).2
      simpa [ColouredPainting.orient, not_iff_not] using this
    · constructor
      · exact fun h' ↦ absurd (hB e h') h3
      · intro h'
        have := hB' _ h'
        rw [hsize e he] at this
        exact absurd this h3
  have hγ : ∀ e, (P.orient B hB).Γ.γ e = if B e then swapTail (P.Γ.γ e) else P.Γ.γ e := fun _ ↦ rfl
  have hγ' : ∀ e, (P'.orient B' hB').Γ.γ e =
    if B' e then swapTail (P'.Γ.γ e) else P'.Γ.γ e := fun _ ↦ rfl
  have hends : ∀ e ∈ P.Γ.E, ∀ (i : ℕ) (hi : i < (P.Γ.γ e).length)
      (hi' : i < (P'.Γ.γ (σe e)).length), (P'.Γ.γ (σe e))[i] ∈ σv (P.Γ.γ e)[i] := by
    intro e he i hi hi'
    by_cases hb : B e
    · have hb' : B' (σe e) := (hsame e he).1 hb
      have he' : σe e ∈ P'.Γ.E := hinf.edge_mem e he
      have h3 := hB e hb
      obtain ⟨a, b, c, habc⟩ := P.Γ.exists_three he h3
      obtain ⟨a', b', c', habc'⟩ := P'.Γ.exists_three he' (by rw [hsize e he, h3])
      have hk := hinf.ends e he
      simp only [hγ, hγ', hb, hb', ite_true, habc, habc', swapTail] at hk
      simp only [habc, habc'] at hi hi' ⊢
      have h0 := hk 0 (by simp) (by simp)
      have h1 := hk 1 (by simp) (by simp)
      have h2 := hk 2 (by simp) (by simp)
      simp only [List.length_cons, List.length_nil] at hi
      interval_cases i
      · exact h0
      · exact h2
      · exact h1
    · have hb' : ¬ B' (σe e) := fun h' ↦ hb ((hsame e he).2 h')
      have hk := hinf.ends e he i
      simp only [hγ, hγ', hb, hb', ite_false] at hk
      exact hk hi hi'
  have hinfl : IsInflation P.Γ P'.Γ σv σe :=
    { edge_mem := hinf.edge_mem
      edge_size := hinf.edge_size
      edge_injOn := hinf.edge_injOn
      vertex_nonempty := hinf.vertex_nonempty
      vertex_subset := hinf.vertex_subset
      vertex_connected := hinf.vertex_connected
      vertex_disjoint := hinf.vertex_disjoint
      ends := hends }
  refine
    { isInflation := hinfl
      respects := h.respects
      le_internal_2 := fun e he hi h2 ↦ (h.le_internal_2 e he hi h2).1
      le_internal_3 := fun e he hi h3 ↦ (h.le_internal_3 e he hi h3).1
      le_border := fun e he s hs hes ↦ (h.le_border e he s hs hes).1
      isLinear :=
        { toIsInflation := hinfl
          borders_iff := h.isLinear.borders_iff
          border_edge := h.isLinear.border_edge
          orientation := fun e he Θ hΘ hne f n n' hn hn' hp ↦ ?_ } }
  have hhead : ((P.orient B hB).Γ.γ e).head? = some n := by
    rw [hγ]
    split_ifs
    · rw [swapTail_head, hn]
    · exact hn
  have hhead' : ((P'.orient B' hB').Γ.γ (σe e)).head? = some n' := by
    rw [hγ']
    split_ifs
    · rw [swapTail_head, hn']
    · exact hn'
  exact h.isLinear.orientation e he Θ hΘ hne f n n' hhead hhead' hp

/-- **Graph Minors XIX, (4.2).** If `χ` is a bad colour scheme, there is an orientedly bad colour
scheme `χ'` with `Σ_{χ'} = Σ_χ`. Here it has the same frame, and its labels are in `α × Bool`. -/
theorem theorem_4_2_proof {χ : ColourScheme S α} (h : χ.IsBad) :
    ∃ χ' : ColourScheme S (α × Bool), χ'.Φ = χ.Φ ∧ χ'.IsOrientedlyBad := by
  classical
  obtain ⟨P, hbad⟩ := h
  refine ⟨χ.orient, rfl, ?_⟩
  by_cases hor : IsOrientableSurface S
  · obtain ⟨ω⟩ := hor
    let B : ℕ → Set S → Prop := fun i e ↦ e ∈ (P i).Γ.E ∧ (tilde e).ncard = 3 ∧
      ∃ a b c, (P i).Γ.γ e = [a, b, c] ∧ ¬ ω.pos (closure e) a b c
    have hB : ∀ i e, B i e → (tilde e).ncard = 3 := fun i e h ↦ h.2.1
    refine ⟨fun i ↦ (P i).orient (B i) (hB i), fun i j hij ⟨σv, σe, hσ⟩ ↦ ?_, Or.inr ⟨ω, ?_⟩⟩
    · exact hbad i j hij ⟨σv, σe, hσ.of_orient⟩
    · intro i e he h3 a b c habc
      have he' : e ∈ (P i).Γ.E := he
      have hγ : ((P i).orient (B i) (hB i)).Γ.γ e =
          if B i e then swapTail ((P i).Γ.γ e) else (P i).Γ.γ e := by
        by_cases hb : B i e
        · rw [ite_eq_left hb]
          exact ite_eq_left hb
        · rw [ite_eq_right hb]
          exact ite_eq_right hb
      obtain ⟨x, y, z, hxyz⟩ := (P i).Γ.exists_three he' h3
      have hnd := (P i).Γ.γ_nodup e he'
      have hset := (P i).Γ.γ_set e he'
      rw [hxyz] at hnd hset
      have hbdry : tilde e ⊆ discBd (closure e) := by
        rcases (P i).Γ.edge_shape e he' with h | h
        · have := h.1
          omega
        · exact h.2.2.2
      have hdisc : IsClosedDisc (closure e) := by
        rcases (P i).Γ.edge_shape e he' with h | h
        · have := h.1
          omega
        · exact h.2.2.1
      have hx : x ∈ tilde e := by rw [← hset]; simp
      have hy : y ∈ tilde e := by rw [← hset]; simp
      have hz : z ∈ tilde e := by rw [← hset]; simp
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, not_false_eq_true, and_true] at hnd
      by_cases hb : B i e
      · rw [hγ, ite_eq_left hb, hxyz] at habc
        simp only [swapTail, List.cons.injEq, and_true] at habc
        obtain ⟨rfl, rfl, rfl⟩ := habc
        obtain ⟨_, _, a', b', c', habc', hneg⟩ := hb
        rw [hxyz] at habc'
        simp only [List.cons.injEq, and_true] at habc'
        obtain ⟨rfl, rfl, rfl⟩ := habc'
        exact (ω.pos_or hdisc (hbdry hx) (hbdry hy) (hbdry hz) hnd.1.1 hnd.1.2 hnd.2).resolve_left
          hneg
      · rw [hγ, ite_eq_right hb, hxyz] at habc
        simp only [List.cons.injEq, and_true] at habc
        obtain ⟨rfl, rfl, rfl⟩ := habc
        by_contra hneg
        exact hb ⟨he', h3, x, y, z, hxyz, hneg⟩
  · refine ⟨fun i ↦ (P i).orient (fun _ ↦ False) (fun _ h ↦ h.elim),
      fun i j hij ⟨σv, σe, hσ⟩ ↦ ?_, Or.inl hor⟩
    exact hbad i j hij ⟨σv, σe, hσ.of_orient⟩

end GraphMinor.GM19
