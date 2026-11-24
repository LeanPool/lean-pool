/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Fan
import LeanPool.GraphMinor.GM11.Regions

/-!
# The rotation at a vertex of a drawing

The papers use freely that the edges and regions at a vertex of a drawing come in a cyclic order.
This file proves what we need of that. Each edge has two ends, so a loop at `v` counts twice: the
*half-edges* at `v` are the pairs `(e, b)` where `b` says which end of `e` is at `v`. Theorem
`exists_rotation` gives a cyclic order `next` on the half-edges at `v`, and a connected set `P k`
off
the drawing for each half-edge `k`, the corner between `k` and `next k`. Near `v` the corners fill
everything off the drawing, and near a point of the edge of `next k` everything off the drawing lies
in the two corners `P k` and `P (next k)`.

The proof takes a small closed disc around `v`, follows each half-edge from `v` until it first
reaches the boundary of the disc, and applies `exists_fanInv` and `sector_sets_props` to these
lines.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A parametrization of all the edges of a drawing, as in `exists_edge_param`. -/
structure EdgePar (Γ : Drawing S) (γ : Set S → I → S) : Prop where
  cont : ∀ e ∈ Γ.E, Continuous (γ e)
  zero : ∀ e ∈ Γ.E, γ e 0 ∈ Γ.V
  one : ∀ e ∈ Γ.E, γ e 1 ∈ Γ.V
  inj : ∀ e ∈ Γ.E, InjOn (γ e) (Ioo 0 1)
  image : ∀ e ∈ Γ.E, γ e '' Ioo 0 1 = e

theorem exists_edgePar [Nonempty S] (Γ : Drawing S) : ∃ γ, EdgePar Γ γ := by
  choose! γ h using fun e (he : e ∈ Γ.E) => exists_edge_param Γ he
  exact ⟨γ, fun e he => (h e he).1, fun e he => (h e he).2.1, fun e he => (h e he).2.2.1,
    fun e he => (h e he).2.2.2.1, fun e he => (h e he).2.2.2.2⟩

/-- The end `0` or `1` of the parameter interval. -/
def endOf (b : Bool) : I := if b then 1 else 0

/-- The half-edges at `v`: an edge with one of its two ends at `v`. A loop gives two half-edges. -/
def halfEdges (Γ : Drawing S) (γ : Set S → I → S) (v : S) : Set (Set S × Bool) :=
  {x | x.1 ∈ Γ.E ∧ γ x.1 (endOf x.2) = v}

theorem finite_halfEdges (Γ : Drawing S) (γ : Set S → I → S) (v : S) :
    (halfEdges Γ γ v).Finite :=
  (Γ.finite_edges.prod (finite_univ (α := Bool))).subset fun _ hx => ⟨hx.1, mem_univ _⟩

/-- Half of a parameter. -/
noncomputable def halfT (t : I) : I :=
  ⟨t.1 / 2, by have := t.2.1; positivity, by have := t.2.2; linarith⟩

/-- The point of parameter `t` on the half of `e` from the end `b`: this is `t / 2` of the way from
that end. -/
noncomputable def halfPar : Bool → I → I
  | true, t => σ (halfT t)
  | false, t => halfT t

theorem continuous_halfPar (b : Bool) : Continuous (halfPar b) := by
  have h : Continuous halfT := Continuous.subtype_mk (by fun_prop) _
  cases b
  · exact h
  · exact unitInterval.continuous_symm.comp h

@[simp] theorem halfPar_zero (b : Bool) : halfPar b 0 = endOf b := by
  have h : halfT 0 = 0 := Subtype.ext (by simp [halfT])
  cases b
  · exact h
  · change σ (halfT 0) = 1
    rw [h]
    simp

theorem halfPar_coe (b : Bool) (t : I) :
    (halfPar b t : ℝ) = if b then 1 - t.1 / 2 else t.1 / 2 := by
  cases b <;> rfl

theorem halfPar_injective (b : Bool) : Function.Injective (halfPar b) := by
  intro s t h
  have h' := congrArg Subtype.val h
  rw [halfPar_coe, halfPar_coe] at h'
  apply Subtype.ext
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h' <;> linarith

theorem halfPar_mem_Ioo (b : Bool) {t : I} (ht : 0 < t) : halfPar b t ∈ Ioo (0 : I) 1 := by
  have ht₁ : (0 : ℝ) < t.1 := ht
  have ht₂ := t.2.2
  have h := halfPar_coe b t
  constructor
  · change (0 : ℝ) < _
    rw [h]
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> linarith
  · change _ < (1 : ℝ)
    rw [h]
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> linarith

theorem halfPar_eq_of_ne {b b' : Bool} (h : b ≠ b') {s t : I} (hst : halfPar b s = halfPar b' t) :
    s = 1 ∧ t = 1 := by
  have h' := congrArg Subtype.val hst
  rw [halfPar_coe, halfPar_coe] at h'
  have hs := s.2.2
  have ht := t.2.2
  cases b <;> cases b' <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h' <;>
    first
    | exact absurd rfl h
    | exact ⟨Subtype.ext (show s.1 = 1 by linarith), Subtype.ext (show t.1 = 1 by linarith)⟩

section Spoke

variable {Γ : Drawing S} {γ : Set S → I → S}

/-- The half-edge `x`, from its end to the middle of the edge. -/
noncomputable def spoke (γ : Set S → I → S) (x : Set S × Bool) (t : I) : S :=
  γ x.1 (halfPar x.2 t)

theorem spoke_mem_edge (hγ : EdgePar Γ γ) {x : Set S × Bool} (hx : x.1 ∈ Γ.E) {t : I} (ht : 0 < t) :
    spoke γ x t ∈ x.1 := by
  have := mem_image_of_mem (γ x.1) (halfPar_mem_Ioo x.2 ht)
  rwa [hγ.image _ hx] at this

omit [TopologicalSpace S] in
theorem spoke_zero (γ : Set S → I → S) (x : Set S × Bool) : spoke γ x 0 = γ x.1 (endOf x.2) := by
  simp [spoke]

theorem continuous_spoke (hγ : EdgePar Γ γ) {x : Set S × Bool} (hx : x.1 ∈ Γ.E) :
    Continuous (spoke γ x) :=
  (hγ.cont _ hx).comp (continuous_halfPar x.2)

theorem edge_notMem_V {e : Set S} (he : e ∈ Γ.E) {x : S} (hx : x ∈ e) : x ∉ Γ.V :=
  (he.2.1 hx).2

theorem spoke_injective (hγ : EdgePar Γ γ) {x : Set S × Bool} (hx : x.1 ∈ Γ.E) :
    Function.Injective (spoke γ x) := by
  intro s t h
  by_cases hs : 0 < s
  · by_cases ht : 0 < t
    · exact halfPar_injective _ (hγ.inj _ hx (halfPar_mem_Ioo _ hs) (halfPar_mem_Ioo _ ht) h)
    · have ht0 : t = 0 := le_antisymm (not_lt.mp ht) (bot_le)
      subst ht0
      rw [spoke_zero] at h
      have hmem := spoke_mem_edge hγ hx hs
      rw [h] at hmem
      have hV : γ x.1 (endOf x.2) ∈ Γ.V := by
        cases hb : x.2
        · exact hγ.zero _ hx
        · exact hγ.one _ hx
      exact absurd hV (edge_notMem_V hx hmem)
  · have hs0 : s = 0 := le_antisymm (not_lt.mp hs) (bot_le)
    subst hs0
    by_cases ht : 0 < t
    · rw [spoke_zero] at h
      have hmem := spoke_mem_edge hγ hx ht
      rw [← h] at hmem
      have hV : γ x.1 (endOf x.2) ∈ Γ.V := by
        cases hb : x.2
        · exact hγ.zero _ hx
        · exact hγ.one _ hx
      exact absurd hV (edge_notMem_V hx hmem)
    · exact (le_antisymm (not_lt.mp ht) bot_le).symm

/-- Different half-edges meet only at the middle of an edge, or at their ends. -/
theorem spoke_eq_of_ne (hγ : EdgePar Γ γ) {x y : Set S × Bool} (hx : x.1 ∈ Γ.E) (hy : y.1 ∈ Γ.E)
    (hxy : x ≠ y) {s t : I} (hs : 0 < s) (ht : 0 < t) (h : spoke γ x s = spoke γ y t) :
    s = 1 ∧ t = 1 := by
  obtain ⟨e, b⟩ := x
  obtain ⟨e', b'⟩ := y
  have h₁ := spoke_mem_edge hγ hx hs
  have h₂ := spoke_mem_edge hγ hy ht
  rw [h] at h₁
  have he : e = e' := Γ.edge_eq_of_mem hx hy h₁ h₂
  subst he
  have hb : b ≠ b' := fun hb => hxy (by rw [hb])
  exact halfPar_eq_of_ne hb (hγ.inj _ hx (halfPar_mem_Ioo b hs) (halfPar_mem_Ioo b' ht) h)

/-- Follow a half-edge from `v` until it first leaves the open set `D'`, in a point of `discBd D`.
-/
theorem exists_truncation (hγ : EdgePar Γ γ) {x : Set S × Bool} (hx : x.1 ∈ Γ.E) {D D' : Set S}
    (hD : IsClosed D) (hD' : IsOpen D') (hsub : D' ⊆ D) (hbd : D \ D' = discBd D)
    (hv : spoke γ x 0 ∈ D') (hout : spoke γ x 1 ∉ D) :
    ∃ τ : I, 0 < τ ∧ τ < 1 ∧ (∀ t, t < τ → spoke γ x t ∈ D') ∧ spoke γ x τ ∈ discBd D := by
  have hc := continuous_spoke hγ hx
  have hC : IsCompact {t : I | spoke γ x t ∉ D'} := (hD'.isClosed_compl.preimage hc).isCompact
  obtain ⟨τ, hτ, hmin⟩ := hC.exists_isLeast ⟨1, fun h => hout (hsub h)⟩
  have hτ0 : 0 < τ := by
    refine unitInterval.pos_iff_ne_zero.mpr ?_
    rintro rfl
    exact hτ hv
  have hbefore : ∀ t, t < τ → spoke γ x t ∈ D' := fun t ht => by
    by_contra hcon
    exact absurd (hmin hcon) (not_le.mpr ht)
  have hτD : spoke γ x τ ∈ D := by
    have h₁ : τ ∈ closure (Iio τ) := by
      rw [closure_Iio' (a := τ) ⟨0, hτ0⟩]
      exact mem_Iic.mpr le_rfl
    have h₂ := map_mem_closure hc h₁ (t := D) fun t ht => hsub (hbefore t ht)
    rwa [hD.closure_eq] at h₂
  have hτ1 : τ < 1 := by
    refine lt_of_le_of_ne le_top ?_
    rintro rfl
    exact hout hτD
  exact ⟨τ, hτ0, hτ1, hbefore, hbd ▸ ⟨hτD, hτ⟩⟩

/-- The piece of a half-edge up to `τ` is a line. -/
theorem isLine_spoke_piece [T2Space S] (hγ : EdgePar Γ γ) {x : Set S × Bool} (hx : x.1 ∈ Γ.E)
    {τ : I} (hτ : 0 < τ) : IsLineWithEnds (spoke γ x '' Icc 0 τ) (spoke γ x 0) (spoke γ x τ) := by
  have hc := continuous_spoke hγ hx
  let f : C(I, S) := ⟨fun t => spoke γ x (t * τ), hc.comp (by fun_prop)⟩
  have hinj : Function.Injective f := by
    intro s t h
    have h₁ := spoke_injective hγ hx h
    have h₂ : s.1 * τ.1 = t.1 * τ.1 := congrArg Subtype.val h₁
    have hτ' : (τ : ℝ) ≠ 0 := ne_of_gt hτ
    exact Subtype.ext (mul_right_cancel₀ hτ' h₂)
  have hr : range f = spoke γ x '' Icc 0 τ := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t * τ, ⟨bot_le, unitInterval.mul_le_right⟩, rfl⟩
    · rintro ⟨t, ⟨-, ht⟩, rfl⟩
      have hτ' : (0 : ℝ) < τ := hτ
      have ht' : t.1 ≤ τ.1 := ht
      refine ⟨⟨t.1 / τ.1, div_nonneg t.2.1 hτ'.le, (div_le_one hτ').mpr ht'⟩, ?_⟩
      change spoke γ x _ = _
      congr 1
      apply Subtype.ext
      change t.1 / τ.1 * τ.1 = t.1
      field_simp
  have := isLineWithEnds_range f hinj
  rw [hr] at this
  have h0 : f 0 = spoke γ x 0 := by simp [f]
  have h1 : f 1 = spoke γ x τ := by simp [f]
  rwa [h0, h1] at this

end Spoke

private theorem isClosed_drawingAwayFromSpokes {Γ : Drawing S} {γ : Set S → I → S}
    (hγ : EdgePar Γ γ) {v : S} (hv : v ∈ Γ.V) [T2Space S]
    (h2 : 2 ≤ Nat.card (halfEdges Γ γ v))
    (τ : halfEdges Γ γ v → I) (hτ0 : ∀ x, 0 < τ x)
    (hvJ : ∀ x : halfEdges Γ γ v, v ∈ spoke γ x.1 '' Icc 0 (τ x)) :
    let H := halfEdges Γ γ v
    let J : H → Set S := fun x => spoke γ x.1 '' Icc 0 (τ x)
    let C : Set S → Set I := fun e => {t | ∀ x : H, x.1.1 = e →
      (if x.1.2 then t.1 ≤ 1 - (τ x).1 / 2 else (τ x).1 / 2 ≤ t.1)}
    let K : Set S := (Γ.V \ {v}) ∪ ⋃ e ∈ Γ.E, γ e '' C e
    IsClosed K ∧ v ∉ K ∧ Γ.U ⊆ K ∪ ⋃ i, J i := by
  classical
  intro H J C K
  have hCclosed : ∀ e, IsClosed (C e) := by
    intro e
    have : C e = ⋂ x : H, {t : I | x.1.1 = e →
        (if x.1.2 then t.1 ≤ 1 - (τ x).1 / 2 else (τ x).1 / 2 ≤ t.1)} := by
      ext t
      simp [C]
    rw [this]
    refine isClosed_iInter fun x => ?_
    by_cases hx : x.1.1 = e
    · cases hb : x.1.2
      · simpa [hx, hb] using isClosed_le continuous_const continuous_subtype_val
      · simpa [hx, hb] using isClosed_le continuous_subtype_val continuous_const
    · simp [hx]
  have hKclosed : IsClosed K := by
    refine ((Γ.finite_V.subset sdiff_subset).isClosed).union ?_
    exact Γ.finite_edges.isClosed_biUnion fun e he =>
      ((hCclosed e).isCompact.image (hγ.cont e he)).isClosed
  have hend : ∀ e ∈ Γ.E, ∀ t : I, t ∉ Ioo (0 : I) 1 → t = 0 ∨ t = 1 := by
    intro e _ t ht
    by_contra hcon
    push Not at hcon
    exact ht ⟨unitInterval.pos_iff_ne_zero.mpr hcon.1, lt_of_le_of_ne le_top hcon.2⟩
  have hvK : v ∉ K := by
    rintro (⟨-, h⟩ | h)
    · exact h rfl
    · obtain ⟨e, he, t, ht, hte⟩ := mem_iUnion₂.mp h
      by_cases hIoo : t ∈ Ioo (0 : I) 1
      · have : v ∈ e := by
          rw [← hγ.image e he]
          exact ⟨t, hIoo, hte⟩
        exact edge_notMem_V he this hv
      · rcases hend e he t hIoo with rfl | rfl
        · have hx : ((e, false) : Set S × Bool) ∈ halfEdges Γ γ v := ⟨he, hte⟩
          have := ht ⟨_, hx⟩ rfl
          simp only [Bool.false_eq_true, ite_false] at this
          have h0 : (0 : ℝ) < τ ⟨_, hx⟩ := hτ0 ⟨_, hx⟩
          simp at this
          linarith
        · have hx : ((e, true) : Set S × Bool) ∈ halfEdges Γ γ v := ⟨he, hte⟩
          have := ht ⟨_, hx⟩ rfl
          simp only [ite_true] at this
          have h0 : (0 : ℝ) < τ ⟨_, hx⟩ := hτ0 ⟨_, hx⟩
          simp at this
          linarith
  have hclosureE : ∀ e ∈ Γ.E, closure e ⊆ γ e '' univ := by
    intro e he
    refine closure_minimal ?_ ((isCompact_univ.image (hγ.cont e he)).isClosed)
    intro x hx
    have h' : x ∈ γ e '' Ioo 0 1 := by rw [hγ.image e he]; exact hx
    obtain ⟨t, -, rfl⟩ := h'
    exact ⟨t, mem_univ _, rfl⟩
  have hUsub : Γ.U ⊆ K ∪ ⋃ i, J i := by
    rw [Γ.U_eq]
    rintro x (hx | hx)
    · by_cases hxv : x = v
      · obtain ⟨k⟩ : Nonempty H := by
          have : 0 < Nat.card H := lt_of_lt_of_le (by norm_num) h2
          exact (Nat.card_pos_iff.mp this).1
        exact Or.inr (mem_iUnion.mpr ⟨k, hxv ▸ hvJ k⟩)
      · exact Or.inl (Or.inl ⟨hx, hxv⟩)
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      obtain ⟨t, -, rfl⟩ := hclosureE e he hxe
      by_cases htC : t ∈ C e
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨e, he, t, htC, rfl⟩))
      · right
        simp only [C, mem_ofPred_eq, not_forall] at htC
        obtain ⟨y, hye, hcon⟩ := htC
        refine mem_iUnion.mpr ⟨y, ?_⟩
        subst hye
        have hy0 := (τ y).2.2
        cases hb : y.1.2
        · rw [hb] at hcon
          simp only [Bool.false_eq_true, ite_false, not_le] at hcon
          have ht0 := t.2.1
          refine ⟨⟨2 * t.1, by linarith, by linarith⟩, ⟨bot_le, ?_⟩, ?_⟩
          · change 2 * t.1 ≤ (τ y).1
            linarith
          · change γ y.1.1 (halfPar y.1.2 _) = _
            rw [hb]
            congr 1
            exact Subtype.ext (by simp [halfPar, halfT])
        · rw [hb] at hcon
          simp only [ite_true, not_le] at hcon
          have ht1 := t.2.2
          refine ⟨⟨2 * (1 - t.1), by linarith, by linarith⟩, ⟨bot_le, ?_⟩, ?_⟩
          · change 2 * (1 - t.1) ≤ (τ y).1
            linarith
          · change γ y.1.1 (halfPar y.1.2 _) = _
            rw [hb]
            congr 1
            exact Subtype.ext (by simp [halfPar, halfT])
  exact ⟨hKclosed, hvK, hUsub⟩

/-- **The rotation at a vertex.** The half-edges at `v`, when there are at least two, have a cyclic
order `next`. Each half-edge `k` has a corner `P k`, the part near `v` between `k` and `next k`. The
corners are connected and miss the drawing, and `v` is in their closure. Near `v`, everything off
the
drawing lies in the corners. At some point `q` of the edge of `next k`, everything near `q` and off
the drawing lies in `P k` and `P (next k)`, and `q` is in the closure of both. -/
theorem exists_rotation_sectors (hS : IsClosedSurface S)
    (Γ : Drawing S) {γ : Set S → I → S} (hγ : EdgePar Γ γ) {v : S}
    (hv : v ∈ Γ.V) (h2 : 2 ≤ Nat.card (halfEdges Γ γ v)) :
    ∃ (next : halfEdges Γ γ v → halfEdges Γ γ v) (P : halfEdges Γ γ v → Set S) (W : Set S)
      (Q : halfEdges Γ γ v → Set S),
      IsOpen W ∧ v ∈ W ∧ Function.Injective next ∧ (∀ k, next k ≠ k) ∧
      (∀ a b, Relation.ReflTransGen (fun x y => y = next x) a b) ∧
      (∀ k, IsPreconnected (P k)) ∧ (∀ k, Disjoint (P k) Γ.U) ∧ (∀ k, v ∈ closure (P k)) ∧
      (W \ Γ.U ⊆ ⋃ k, P k) ∧
      (∀ k, ∃ q ∈ (next k).1.1, ∃ O, IsOpen O ∧ q ∈ O ∧ O \ Γ.U ⊆ P k ∪ P (next k) ∧
        q ∈ closure (P k) ∧ q ∈ closure (P (next k))) ∧
      (∀ k, IsClosedDisc (Q k) ∧ v ∈ discBd (Q k) ∧ P k ⊆ Q k ∧ (W ∩ Q k) \ discBd (Q k) ⊆ P k) ∧
      (∀ k j, k ≠ j → Q k ∩ Q j ⊆ Γ.U) ∧
      (∀ k (i : halfEdges Γ γ v), i ≠ k → i ≠ next k → ∀ t : I, 0 < t → spoke γ i.1 t ∈ W →
        spoke γ i.1 t ∉ Q k) ∧
      (∀ k, W ∩ discBd (Q k) ⊆ Γ.U) ∧
      ∃ τ : halfEdges Γ γ v → I, (∀ k, 0 < τ k) ∧
        (∀ k t, t ≤ τ k → spoke γ k.1 t ∈ discBd (Q k)) ∧
        ∀ k t, t ≤ τ (next k) → spoke γ (next k).1 t ∈ discBd (Q k) := by
  classical
  have : T2Space S := hS.2.1
  have : Fintype (halfEdges Γ γ v) := (finite_halfEdges Γ γ v).fintype
  let H := halfEdges Γ γ v
  have hmidE : ∀ x : H, spoke γ x.1 1 ∈ x.1.1 := fun x =>
    spoke_mem_edge hγ x.2.1 (by simp)
  have hmidfin : (range fun x : H => spoke γ x.1 1).Finite := finite_range _
  have hvmid : v ∉ range fun x : H => spoke γ x.1 1 := by
    rintro ⟨x, hx⟩
    exact edge_notMem_V x.2.1 (hmidE x) (by rw [show spoke γ x.1 1 = v from hx]; exact hv)
  obtain ⟨D, D', hD, hD', hvD', hD'D, hDO, hbdD⟩ :=
    exists_closedDisc_nbhd hS hmidfin.isClosed.isOpen_compl hvmid
  have hDc : IsClosed D := hD.isClosed
  have hspoke0 : ∀ x : H, spoke γ x.1 0 = v := fun x => by rw [spoke_zero]; exact x.2.2
  have htrunc : ∀ x : H, ∃ τ : I, 0 < τ ∧ τ < 1 ∧ (∀ t, t < τ → spoke γ x.1 t ∈ D') ∧
      spoke γ x.1 τ ∈ discBd D := fun x =>
    exists_truncation hγ x.2.1 hDc hD' hD'D hbdD (by rw [hspoke0]; exact hvD')
      fun h => hDO h ⟨x, rfl⟩
  choose τ hτ0 hτ1 hτb hτp using htrunc
  let J : H → Set S := fun x => spoke γ x.1 '' Icc 0 (τ x)
  let p : H → S := fun x => spoke γ x.1 (τ x)
  have hbdD' : Disjoint D' (discBd D) := by
    rw [← hbdD]
    exact Set.disjoint_left.mpr fun x hx hx' => hx'.2 hx
  have hvJ : ∀ i, v ∈ J i := fun i => ⟨0, ⟨le_rfl, bot_le⟩, hspoke0 i⟩
  have hline : ∀ i, IsLineWithEnds (J i) v (p i) := fun i => by
    have := isLine_spoke_piece hγ i.2.1 (hτ0 i)
    rwa [hspoke0] at this
  have hbdJ : ∀ i (t : I), t ≤ τ i → spoke γ i.1 t ∈ D := by
    intro i t ht
    rcases ht.eq_or_lt with rfl | ht
    · exact discBd_subset _ (hτp i)
    · exact hD'D (hτb i t ht)
  have hsub : ∀ i, J i ⊆ D := by
    rintro i _ ⟨t, ht, rfl⟩
    exact hbdJ i t ht.2
  have hbd : ∀ i, J i ∩ discBd D = {p i} := by
    intro i
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hx⟩
      rcases ht.2.eq_or_lt with rfl | hlt
      · rfl
      · exact absurd hx (Set.disjoint_left.mp hbdD' (hτb i t hlt))
    · rintro rfl
      exact ⟨⟨τ i, ⟨bot_le, le_rfl⟩, rfl⟩, hτp i⟩
  have hJJ : ∀ i j, i ≠ j → J i ∩ J j = {v} := by
    intro i j hij
    ext x
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, ⟨t, ht, hst⟩⟩
      by_cases hs0 : 0 < s
      · by_cases ht0 : 0 < t
        · have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
          have := (spoke_eq_of_ne hγ i.2.1 j.2.1 hne hs0 ht0 hst.symm).1
          have hs1 : s < 1 := lt_of_le_of_lt hs.2 (hτ1 i)
          exact absurd this hs1.ne
        · have ht' : t = 0 := le_antisymm (not_lt.mp ht0) bot_le
          rw [← hst, ht', hspoke0]
          rfl
      · have hs' : s = 0 := le_antisymm (not_lt.mp hs0) bot_le
        rw [hs', hspoke0]
        rfl
    · rintro rfl
      exact ⟨hvJ i, hvJ j⟩
  have hne : ∀ i, v ≠ p i := fun i h =>
    edge_notMem_V i.2.1 (spoke_mem_edge hγ i.2.1 (hτ0 i))
      (by rw [show spoke γ i.1 (τ i) = v from h.symm]; exact hv)
  have hvD : v ∉ discBd D := fun h => Set.disjoint_left.mp hbdD' hvD' h
  obtain ⟨next, Q, hF⟩ := exists_fanInv hD hline hsub hbd hJJ hne hvD (Finset.univ : Finset H)
    (by rwa [Finset.card_univ, ← Nat.card_eq_fintype_card])
  -- The rest of the drawing.
  let C : Set S → Set I := fun e => {t | ∀ x : H, x.1.1 = e →
    (if x.1.2 then t.1 ≤ 1 - (τ x).1 / 2 else (τ x).1 / 2 ≤ t.1)}
  let K : Set S := (Γ.V \ {v}) ∪ ⋃ e ∈ Γ.E, γ e '' C e
  obtain ⟨hKclosed, hvK, hUsub⟩ := isClosed_drawingAwayFromSpokes hγ hv h2 τ hτ0 hvJ
  change IsClosed K at hKclosed
  change v ∉ K at hvK
  change Γ.U ⊆ K ∪ ⋃ i, J i at hUsub
  have hJU : ∀ i, J i ⊆ Γ.U := by
    rintro i _ ⟨t, -, rfl⟩
    by_cases ht : 0 < t
    · exact Γ.closure_subset_U i.2.1 (subset_closure (spoke_mem_edge hγ i.2.1 ht))
    · have : t = 0 := le_antisymm (not_lt.mp ht) bot_le
      rw [this, hspoke0]
      exact Γ.V_subset_U hv
  obtain ⟨P, W, hW, hvW, hWG, hP⟩ := exists_sector_sets hF (hD'.inter hKclosed.isOpen_compl)
    ⟨hvD', hvK⟩ hvJ hKclosed hvK
  have hWD' : W ⊆ D' := hWG.trans inter_subset_left
  have hWK : Disjoint W K := disjoint_left.mpr fun x hx => (hWG hx).2
  have hWbd : Disjoint W (discBd D) := hbdD'.mono_left hWD'
  have hWD : W ⊆ D := hWD'.trans hD'D
  obtain ⟨c₁, c₂⟩ := sector_sets_props hF hW hWD hWbd
    (fun k hk => (hF.disc k hk).isClosed)
    (fun k hk => ⟨(hP k hk).2.2.2.2.1, (hP k hk).2.2.2.2.2⟩)
  have mem : ∀ k : H, k ∈ (Finset.univ : Finset H) := Finset.mem_univ
  have hiU : (⋃ i ∈ (Finset.univ : Finset H), J i) ⊆ Γ.U :=
    iUnion₂_subset fun i _ => hJU i
  have hvbd : ∀ k, v ∈ discBd (Q k) := by
    intro k
    obtain ⟨B, -, hb⟩ := hF.bd k (mem k)
    exact hb ▸ Or.inl (Or.inl (hvJ k))
  have hdisjU : ∀ k, Disjoint (P k) Γ.U := by
    intro k
    obtain ⟨-, hPQ, hPbd, hPK, -, -⟩ := hP k (mem k)
    refine Set.disjoint_left.mpr fun x hx hxU => ?_
    obtain ⟨B, hBD, hb⟩ := hF.bd k (mem k)
    have hxbd : x ∉ discBd (Q k) := Set.disjoint_left.mp hPbd hx
    rw [hb] at hxbd
    rcases hUsub hxU with hxK | hxJ
    · exact Set.disjoint_left.mp hPK hx hxK
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hxJ
      by_cases hik : i = k
      · exact hxbd (Or.inl (Or.inl (hik ▸ hi)))
      · by_cases hin : i = next k
        · exact hxbd (Or.inl (Or.inr (hin ▸ hi)))
        · rcases hF.off k (mem k) i (mem i) hik hin ⟨hi, hPQ hx⟩ with h | h
          · have : x = v := h
            exact hxbd (Or.inl (Or.inl (this ▸ hvJ k)))
          · have := hF.edge k (mem k) ⟨hPQ hx, h⟩
            rw [hb] at this
            exact hxbd this
  refine ⟨next, P, W, Q, hW, hvW, ?_, fun k => hF.next_ne k (mem k), ?_, fun k => (hP k (mem k)).1,
    hdisjU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, τ, hτ0, ?_, ?_⟩
  · intro a b he
    exact hF.next_inj a (mem a) b (mem b) he
  · intro a b
    exact hF.reach a (mem a) b (mem b)
  · intro k
    exact (hP k (mem k)).2.2.2.2.2 ⟨hvW, hvbd k⟩
  · rintro x ⟨hxW, hxU⟩
    obtain ⟨k, -, hk⟩ := mem_iUnion₂.mp
      (c₁ ⟨hxW, fun h => hxU (hiU h)⟩)
    exact mem_iUnion.mpr ⟨k, hk⟩
  · intro k
    have hl := next k
    have hmem := IsLineWithEnds.mem_closure_sdiff (hline (next k))
    obtain ⟨q, hqW, hqJ, hqv⟩ := mem_closure_iff.mp hmem W hW hvW
    obtain ⟨t, ht, rfl⟩ := hqJ
    have ht0 : 0 < t := by
      refine unitInterval.pos_iff_ne_zero.mpr ?_
      rintro rfl
      exact hqv (hspoke0 _)
    obtain ⟨O, hO, hqO, hsubO, hcl₁, hcl₂⟩ := c₂ k (mem k) _ ⟨hqW, ⟨t, ht, rfl⟩⟩ hqv
    exact ⟨_, spoke_mem_edge hγ (next k).2.1 ht0, O, hO, hqO,
      fun x hx => hsubO ⟨hx.1, fun h => hx.2 (hiU h)⟩, hcl₁, hcl₂⟩
  · intro k
    obtain ⟨-, hPQ, -, -, hsubP, -⟩ := hP k (mem k)
    exact ⟨hF.disc k (mem k), hvbd k, hPQ, hsubP⟩
  · intro k j hkj x hx
    obtain ⟨i, -, hi⟩ := mem_iUnion₂.mp (hF.inter k (mem k) j (mem j) hkj hx)
    exact hJU i hi
  · intro k i hik hin t ht hW' hQ
    have hmem : spoke γ i.1 t ∈ i.1.1 := spoke_mem_edge hγ i.2.1 ht
    have hne : spoke γ i.1 t ≠ v := fun h => edge_notMem_V i.2.1 hmem (by rw [h]; exact hv)
    have hWbd : Disjoint W (discBd D) := hbdD'.mono_left hWD'
    have hU : spoke γ i.1 t ∈ Γ.U := Γ.closure_subset_U i.2.1 (subset_closure hmem)
    rcases hUsub hU with hK | hJ
    · exact disjoint_left.mp hWK hW' hK
    obtain ⟨i', hi'⟩ := mem_iUnion.mp hJ
    have hkey : ∀ j : H, j ≠ i → spoke γ i.1 t ∉ J j := by
      rintro j hji ⟨s, hs, hst⟩
      have hs0 : 0 < s := by
        refine unitInterval.pos_iff_ne_zero.mpr ?_
        rintro rfl
        exact hne (hst.symm.trans (hspoke0 j))
      have hne' : j.1 ≠ i.1 := fun h => hji (Subtype.ext h)
      have := (spoke_eq_of_ne hγ j.2.1 i.2.1 hne' hs0 ht hst).1
      exact absurd this (lt_of_le_of_lt hs.2 (hτ1 j)).ne
    have hi'i : i' = i := by
      by_contra h
      exact hkey i' h hi'
    subst hi'i
    rcases hF.off k (mem k) i' (mem i') hik hin ⟨hi', hQ⟩ with h | h
    · exact hne h
    · exact disjoint_left.mp hWbd hW' h
  · intro k x hx
    obtain ⟨B, hB', hb⟩ := hF.bd k (mem k)
    rw [hb] at hx
    rcases hx.2 with (h | h) | h
    · exact hJU _ h
    · exact hJU _ h
    · exact (disjoint_left.mp hWbd hx.1 (hB' h)).elim
  · intro k t ht
    obtain ⟨B, -, hb⟩ := hF.bd k (mem k)
    rw [hb]
    exact Or.inl (Or.inl ⟨t, ⟨bot_le, ht⟩, rfl⟩)
  · intro k t ht
    obtain ⟨B, -, hb⟩ := hF.bd k (mem k)
    rw [hb]
    exact Or.inl (Or.inr ⟨t, ⟨bot_le, ht⟩, rfl⟩)

/-- The cyclic order at a vertex, without the sectors of `exists_rotation_sectors`. -/
theorem exists_rotation (hS : IsClosedSurface S)
    (Γ : Drawing S) {γ : Set S → I → S} (hγ : EdgePar Γ γ) {v : S}
    (hv : v ∈ Γ.V) (h2 : 2 ≤ Nat.card (halfEdges Γ γ v)) :
    ∃ (next : halfEdges Γ γ v → halfEdges Γ γ v) (P : halfEdges Γ γ v → Set S) (W : Set S),
      IsOpen W ∧ v ∈ W ∧ Function.Injective next ∧ (∀ k, next k ≠ k) ∧
      (∀ a b, Relation.ReflTransGen (fun x y => y = next x) a b) ∧
      (∀ k, IsPreconnected (P k)) ∧ (∀ k, Disjoint (P k) Γ.U) ∧ (∀ k, v ∈ closure (P k)) ∧
      (W \ Γ.U ⊆ ⋃ k, P k) ∧
      ∀ k, ∃ q ∈ (next k).1.1, ∃ O, IsOpen O ∧ q ∈ O ∧ O \ Γ.U ⊆ P k ∪ P (next k) ∧
        q ∈ closure (P k) ∧ q ∈ closure (P (next k)) := by
  obtain ⟨next, P, W, -, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, -, -, -, -, -⟩ :=
    exists_rotation_sectors hS Γ hγ hv h2
  exact ⟨next, P, W, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀⟩

end GraphMinor.GM11
