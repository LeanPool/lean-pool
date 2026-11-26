/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section9c
public import LeanPool.GraphMinor.GM20.Codes

/-!
# Graph Minors XX, Section 9: the labels of cells

This file gives the well-quasi-order `Ω₁` of the proof of (9.1), and the label `ψ(c)` of each cell
of a
hull. An internal cell keeps its label `φ(c)`. A border cell gets `φ(c)` and a finite code, which
records
through positions in `μ(c)` the two nodes of `c`, the marches of `β(n₁)` and `β(n₂)`, the patch
`Δ(c)`,
and whether `c = c_Θ`.

From now on `ζ` is a linear inflation with `ψ(c) ≤ ψ'(ζ(c))` for all `c`. We deduce claim (1) of the
paper,
and that a cell and its image are aligned (`Aligned`): the bijection from `μ(c)` to `μ'(ζ(c))`
respects
everything in the code.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface GraphMinor.GM04 GraphMinor.GM18 GraphMinor.GM10 Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-- The type of finite codes of border cells. -/
abbrev CellCode (K : ℕ) : Type :=
  Prop × Set (Fin K × Fin K) × Set (Fin K × Fin K) × Set (Fin K × Fin K) × Set (Fin K × Fin K) ×
    Set (Set (Fin K) × Set (Fin K × Fin K))

instance (K : ℕ) : Finite (CellCode K) := inferInstance

/-- The well-quasi-order `Ω₁` of the proof of (9.1). -/
abbrev LabelOrder (Ω : Type*) (K : ℕ) : Type _ :=
  DisjointUnionQuasiOrder Ω (Ω × Discrete (CellCode K))

theorem wqo_labelOrder {Ω : Type*} [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω) (K : ℕ) :
    WellQuasiOrderedLE (LabelOrder Ω K) := by
  have h₂ : WellQuasiOrderedLE (Discrete (CellCode K)) := wqo_discrete _
  exact wqo_disjointUnion hΩ inferInstance

section Label

variable {Ω : Type*} {X : GradedSurface} {F : CuffParam X.S} {Q : Patchwork Ω α β}
  (A : Side X F Q)

/-- `c` is the cell `c_Θ` for some cuff `Θ`. -/
def Side.IsCut (c : Set X.S) : Prop :=
  ∃ Θ, ∃ hΘ : Θ ∈ cuffs X.S, c = (A.C Θ hΘ).cell ((A.C Θ hΘ).k - 1)

/-- The march of the `i`th node of `c`. -/
def Side.termπ (c : Set X.S) (i : ℕ) : List α := ((A.Γ.γ c)[i]?).elim [] A.π

/-- The code of a border cell. -/
noncomputable def Side.code (K : ℕ) (c : Set X.S) : CellCode K :=
  (A.IsCut c,
    marchCode K (Q.μ (A.h.cell c)) (Q.μ (A.h.cell c)),
    marchCode K (Q.μ (A.h.cell c)) ((A.Γ.γ c).map A.h.node),
    marchCode K (Q.μ (A.h.cell c)) (A.termπ c 0),
    marchCode K (Q.μ (A.h.cell c)) (A.termπ c 1),
    patchCode K (Q.μ (A.h.cell c)) (Q.Δ (A.h.cell c)))

open Classical in
/-- The label `ψ(c)`. -/
noncomputable def Side.ψ (K : ℕ) (c : Set X.S) : LabelOrder Ω K :=
  if Painting.IsBorder c then Sum.inr (Q.φ (A.h.cell c), A.code K c) else Sum.inl (Q.φ (A.h.cell c))

theorem Side.ψ_border (K : ℕ) {c : Set X.S} (hb : Painting.IsBorder c) :
    A.ψ K c = Sum.inr (Q.φ (A.h.cell c), A.code K c) := by
  classical
  exact ite_eq_left hb

theorem Side.ψ_internal (K : ℕ) {c : Set X.S} (hb : ¬ Painting.IsBorder c) :
    A.ψ K c = Sum.inl (Q.φ (A.h.cell c)) := by
  classical
  exact ite_eq_right hb

end Label

theorem Painting.isBorder_image {S : Type} [TopologicalSpace S] {Γ Γ' : Painting S} {ζn : S → Set S}
    {ζc : Set S → Set S} (hζ : IsLinearInflation Γ Γ' ζn ζc) {c : Set S} (hc : c ∈ Γ.C) :
    Painting.IsBorder (ζc c) ↔ Painting.IsBorder c := by
  constructor
  · intro h
    obtain ⟨Θ, hΘ, hm⟩ := exists_cuff_of_isBorder h
    obtain ⟨y, hy, hyΘ⟩ := (hζ.borders_iff c hc Θ hΘ).mpr hm
    exact ⟨y, hy, cuff_subset_bd hΘ hyΘ⟩
  · intro h
    obtain ⟨Θ, hΘ, hm⟩ := exists_cuff_of_isBorder h
    obtain ⟨y, hy, hyΘ⟩ := (hζ.borders_iff c hc Θ hΘ).mp hm
    exact ⟨y, hy, cuff_subset_bd hΘ hyΘ⟩

/-- Two equal marches of positions give the same position of a common vertex. -/
theorem term_of_code {K : ℕ} {r r' m₁ m₂ m₁' m₂' : List α} (hr : r.length ≤ K)
    (h₁ : marchCode K r m₁ = marchCode K r' m₁') (h₂ : marchCode K r m₂ = marchCode K r' m₂')
    (hl₁ : m₁.length ≤ K) (hl₂ : m₂.length ≤ K) {i j : ℕ} {x : α} (hx : x ∈ r)
    (hm₁ : m₁[i]? = some x) (hm₂ : m₂[j]? = some x) :
    ∃ x', m₁'[i]? = some x' ∧ m₂'[j]? = some x' := by
  obtain ⟨q, hq⟩ := exists_index hr hx
  obtain ⟨y₁, hy₁, hq₁⟩ := marchCode_forward h₁ hl₁ hm₁ hq
  obtain ⟨y₂, hy₂, hq₂⟩ := marchCode_forward h₂ hl₂ hm₂ hq
  have : y₁ = y₂ := by
    rw [hq₁] at hq₂
    exact Option.some.inj hq₂
  subst this
  exact ⟨y₁, hy₁, hy₂⟩

section Inflation

variable {Ω : Type*} [Preorder Ω] {X : GradedSurface} {F : CuffParam X.S} {Q Q' : Patchwork Ω α β}
  (A : Side X F Q) (A' : Side X F Q') {ζn : X.S → Set X.S} {ζc : Set X.S → Set X.S} {K : ℕ}

/-- The relation of `ψ` gives the relation of labels. -/
theorem φ_le_of_ψ {c : Set X.S} (hc : c ∈ A.Γ.C) (hζ : IsLinearInflation A.Γ A'.Γ ζn ζc)
    (h : A.ψ K c ≤ A'.ψ K (ζc c)) : Q.φ (A.h.cell c) ≤ Q'.φ (A'.h.cell (ζc c)) := by
  classical
  by_cases hb : Painting.IsBorder c
  · have hb' := (Painting.isBorder_image hζ hc).mpr hb
    rw [A.ψ_border K hb, A'.ψ_border K hb'] at h
    cases h with
    | inr h₁ => exact h₁.1
  · have hb' : ¬ Painting.IsBorder (ζc c) := fun h₁ ↦ hb ((Painting.isBorder_image hζ hc).mp h₁)
    rw [A.ψ_internal K hb, A'.ψ_internal K hb'] at h
    cases h with
    | inl h₁ => exact h₁

/-- The relation of `ψ` gives the equality of codes. -/
theorem code_eq_of_ψ {c : Set X.S} (hc : c ∈ A.Γ.C) (hb : Painting.IsBorder c)
    (hζ : IsLinearInflation A.Γ A'.Γ ζn ζc) (h : A.ψ K c ≤ A'.ψ K (ζc c)) :
    A.code K c = A'.code K (ζc c) := by
  classical
  have hb' := (Painting.isBorder_image hζ hc).mpr hb
  rw [A.ψ_border K hb, A'.ψ_border K hb'] at h
  cases h with
  | inr h₁ => exact h₁.2

/-- Claim (1) of the proof of (9.1): `ζ(c_Θ) = c'_Θ`. -/
theorem cut_image (hζ : IsLinearInflation A.Γ A'.Γ ζn ζc)
    (hψ : ∀ c ∈ A.Γ.C, A.ψ K c ≤ A'.ψ K (ζc c)) {Θ : Set X.S} (hΘ : Θ ∈ cuffs X.S) :
    ζc ((A.C Θ hΘ).cell ((A.C Θ hΘ).k - 1)) = (A'.C Θ hΘ).cell ((A'.C Θ hΘ).k - 1) := by
  set c := (A.C Θ hΘ).cell ((A.C Θ hΘ).k - 1) with hcdef
  have hc : c ∈ A.Γ.C := (A.C Θ hΘ).cell_mem _
  have hm : (c ∩ Θ).Nonempty := (A.C Θ hΘ).meets _
  obtain ⟨y₀, hy₀, hy₀Θ⟩ := hm
  have hb : Painting.IsBorder c := ⟨y₀, hy₀, cuff_subset_bd hΘ hy₀Θ⟩
  have hcode := code_eq_of_ψ A A' hc hb hζ (hψ c hc)
  have hcut : A.IsCut c := ⟨Θ, hΘ, rfl⟩
  have hiff : A.IsCut c = A'.IsCut (ζc c) := congrArg Prod.fst hcode
  obtain ⟨Θ₂, hΘ₂, heq⟩ := (hiff ▸ hcut : A'.IsCut (ζc c))
  have hmeet := (hζ.borders_iff c hc Θ hΘ).mp ⟨y₀, hy₀, hy₀Θ⟩
  have hmeet₂ : (ζc c ∩ Θ₂).Nonempty := by
    rw [heq]
    exact (A'.C Θ₂ hΘ₂).meets _
  obtain ⟨y, hy, hyΘ₂⟩ := hmeet₂
  have hyΘ : y ∈ Θ := closure_inter_bd_subset A'.Γ (hζ.cell_mem c hc) hΘ hmeet
    ⟨subset_closure hy, cuff_subset_bd hΘ₂ hyΘ₂⟩
  obtain rfl := cuff_eq_of_mem hΘ hΘ₂ hyΘ hyΘ₂
  exact heq

/-- `c` and `c'` are aligned: the bijection from `μ(c)` to `μ'(c')` maps the nodes `a, b` of `c` to
the
nodes `a', b'` of `c'`, and the marches `π(a), π(b)` to `π'(a'), π'(b')`. -/
structure Aligned (K : ℕ) (c c' : Set X.S) (a b a' b' : X.S) : Prop where
  length_eq : (Q.μ (A.h.cell c)).length = (Q'.μ (A'.h.cell c')).length
  code₁ : marchCode K (Q.μ (A.h.cell c)) (A.π a) = marchCode K (Q'.μ (A'.h.cell c')) (A'.π a')
  code₂ : marchCode K (Q.μ (A.h.cell c)) (A.π b) = marchCode K (Q'.μ (A'.h.cell c')) (A'.π b')
  node₁ : ∀ q : Fin K, (Q.μ (A.h.cell c))[q.1]? = some (A.h.node a) →
    (Q'.μ (A'.h.cell c'))[q.1]? = some (A'.h.node a')
  node₂ : ∀ q : Fin K, (Q.μ (A.h.cell c))[q.1]? = some (A.h.node b) →
    (Q'.μ (A'.h.cell c'))[q.1]? = some (A'.h.node b')

variable {A A'}

omit [Preorder Ω] in
theorem Aligned.swap {c c' : Set X.S} {a b a' b' : X.S} (h : Aligned A A' K c c' a b a' b') :
    Aligned A A' K c c' b a b' a' :=
  ⟨h.length_eq, h.code₂, h.code₁, h.node₂, h.node₁⟩

variable (A A')

omit [Preorder Ω] in
/-- For a border cell `c` with march `[a, b]`, whose image has march `[a', b']`, the two cells are
aligned. -/
theorem aligned_of_code {c c' : Set X.S} {a b a' b' : X.S} (hγ : A.Γ.γ c = [a, b])
    (hγ' : A'.Γ.γ c' = [a', b']) (hcode : A.code K c = A'.code K c') (hK : 2 ≤ K)
    (hr : (Q.μ (A.h.cell c)).length ≤ K) (hr' : (Q'.μ (A'.h.cell c')).length ≤ K)
    (hnd : (Q.μ (A.h.cell c)).Nodup) (hnd' : (Q'.μ (A'.h.cell c')).Nodup) :
    Aligned A A' K c c' a b a' b' := by
  simp only [Side.code, Prod.mk.injEq] at hcode
  obtain ⟨-, h₀, h₁, h₂, h₃, -⟩ := hcode
  have hl : (A.Γ.γ c).map A.h.node = [A.h.node a, A.h.node b] := by rw [hγ]; rfl
  have hl' : (A'.Γ.γ c').map A'.h.node = [A'.h.node a', A'.h.node b'] := by rw [hγ']; rfl
  have ht₀ : A.termπ c 0 = A.π a := by simp [Side.termπ, hγ]
  have ht₁ : A.termπ c 1 = A.π b := by simp [Side.termπ, hγ]
  have ht₀' : A'.termπ c' 0 = A'.π a' := by simp [Side.termπ, hγ']
  have ht₁' : A'.termπ c' 1 = A'.π b' := by simp [Side.termπ, hγ']
  rw [hl, hl'] at h₁
  rw [ht₀, ht₀'] at h₂
  rw [ht₁, ht₁'] at h₃
  refine ⟨length_eq_of_code hr hr' hnd hnd' (fun _ h ↦ h) (fun _ h ↦ h) h₀, h₂, h₃,
    fun q hq ↦ ?_, fun q hq ↦ ?_⟩
  · obtain ⟨y, hy, hq'⟩ := marchCode_forward h₁ (p := 0) (by simpa using hK) rfl hq
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
    rwa [← hy] at hq'
  · obtain ⟨y, hy, hq'⟩ := marchCode_forward h₁ (p := 1) (by simpa using hK) rfl hq
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hy
    rwa [← hy] at hq'

/-- The marches `μ(c)` of border cells have at most `K` terms. -/
def Side.Bounded (K : ℕ) : Prop :=
  ∀ c ∈ A.Γ.C, Painting.IsBorder c → (Q.μ (A.h.cell c)).length ≤ K

omit [Preorder Ω] in
theorem Side.μ_nodup {c : Set X.S} (hc : c ∈ A.Γ.C) : (Q.μ (A.h.cell c)).Nodup := by
  refine Q.μ_nodup _ ?_
  rw [A.dom_eq]
  exact A.h.cell_bijOn.mapsTo hc

/-- If `ζ(cell m) = cell' m'` then the two cells are aligned, with `pos m, pos (m + 1)` going to
`pos' m', pos' (m' + 1)`. -/
theorem aligned_cell (hζ : IsLinearInflation A.Γ A'.Γ ζn ζc)
    (hψ : ∀ c ∈ A.Γ.C, A.ψ K c ≤ A'.ψ K (ζc c)) (hK : 2 ≤ K) (hB : A.Bounded K) (hB' : A'.Bounded K)
    {Θ : Set X.S} (hΘ : Θ ∈ cuffs X.S) {m m' : ℕ}
    (h : ζc ((A.C Θ hΘ).cell m) = (A'.C Θ hΘ).cell m') :
    Aligned A A' K ((A.C Θ hΘ).cell m) ((A'.C Θ hΘ).cell m') ((A.C Θ hΘ).pos m)
      ((A.C Θ hΘ).pos (m + 1)) ((A'.C Θ hΘ).pos m') ((A'.C Θ hΘ).pos (m' + 1)) := by
  set C := A.C Θ hΘ
  set C' := A'.C Θ hΘ
  have hc := C.cell_mem m
  obtain ⟨y, hy, hyΘ⟩ := C.meets m
  have hb : Painting.IsBorder (C.cell m) := ⟨y, hy, cuff_subset_bd hΘ hyΘ⟩
  have hb' : Painting.IsBorder (C'.cell m') := h ▸ (Painting.isBorder_image hζ hc).mpr hb
  have hcode : A.code K (C.cell m) = A'.code K (C'.cell m') :=
    h ▸ code_eq_of_ψ A A' hc hb hζ (hψ _ hc)
  have hr := hB _ hc hb
  have hr' := hB' _ (C'.cell_mem m') hb'
  have hnd := A.μ_nodup hc
  have hnd' := A'.μ_nodup (C'.cell_mem m')
  obtain ⟨h₁, h₂⟩ := image_cell hζ hΘ C C' h
  have hdis := hζ.node_disjoint _ (C.mem_N m) _ (C.mem_N (m + 1)) (C.pos_ne_succ m)
  have hnode : ∀ (u v u' v' : X.S), A.Γ.γ (C.cell m) = [u, v] → A'.Γ.γ (C'.cell m') = [u', v'] →
      u ∈ A.Γ.N → u' ∈ ζn u := by
    intro u v u' v' hu hu' hN
    have h₃ := hζ.nodes u hN _ hc 0 (by rw [hu]; simp) (by rw [h, hu']; simp)
    simp only [h, hu, hu'] at h₃
    exact h₃.mp (by simp)
  rcases C.γ_eq m with h₃ | h₃ <;> rcases C'.γ_eq m' with h₄ | h₄
  · exact aligned_of_code A A' h₃ h₄ hcode hK hr hr' hnd hnd'
  · exact absurd h₂ (Set.disjoint_left.mp hdis (hnode _ _ _ _ h₃ h₄ (C.mem_N m)))
  · exact absurd h₁ (Set.disjoint_right.mp hdis (hnode _ _ _ _ h₃ h₄ (C.mem_N (m + 1))))
  · exact (aligned_of_code A A' h₃ h₄ hcode hK hr hr' hnd hnd').swap

end Inflation

end GraphMinor.GM20
