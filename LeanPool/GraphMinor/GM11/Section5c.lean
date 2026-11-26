/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.CircuitRegions

/-!
# Graph Minors XI, statement (5.4)

The main result is `theorem_5_4`: if `(Z₁, Z₂, Z₃)` is a partition of `R(Γ)`, then one of `Z₁, Z₂,
Z₃`
is not small. With `theorem_5_5_of_partition` this gives (5.5) (`theorem_5_5`).

We follow the paper's proof (pages 82–86) up to its statement (8): a counterexample with `N(Z₁, Z₂,
Z₃)`
minimal has `N(Z_i)` a circuit `C_i` and `Z_i` the set of regions in `ins(C_i)`. The paper then
shows that
every circuit of `K = C₁ ∪ C₂ ∪ C₃` is null-homotopic, so that `Σ` is a sphere and `K` is three
paths
with the same ends. We replace this homotopy step by the same argument modulo 2, which needs no
topology beyond the discs `ins(C)`. A circuit `T` of `K` of length `< 2θ` has `N(A) = T` for the set
`A` of regions in `ins(T)`. Since
each `ins(C_i) - U(C_i)` is connected and misses `U(T)`, the set `A` is a union of some of the
`Z_i`, and so
`T` is one of `C₁, C₂, C₃`. Then `exists_theta` gives the three paths directly, and the second slope
axiom
gives the contradiction, as in the paper.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S] {Γ : Drawing S} {k ω : ℕ} {ins : Drawing S → Set S}
  {Ω : Set S}

/-- Three small sets that partition `R(Γ)`. -/
structure IsTriple [T1Space S] (Γ : Drawing S) (ins : Drawing S → Set S) (k : ℕ) (Ω : Set S) (ω : ℕ)
    (Z₁ Z₂ Z₃ : Set (Set S)) : Prop where
  cover : Z₁ ∪ Z₂ ∪ Z₃ = Γ.R
  d₁₂ : Disjoint Z₁ Z₂
  d₁₃ : Disjoint Z₁ Z₃
  d₂₃ : Disjoint Z₂ Z₃
  s₁ : IsSmall Γ ins k Ω ω Z₁
  s₂ : IsSmall Γ ins k Ω ω Z₂
  s₃ : IsSmall Γ ins k Ω ω Z₃

/-- The edges of `N(Z₁, Z₂, Z₃)`. -/
def tripleE [T1Space S] (Γ : Drawing S) (Z₁ Z₂ Z₃ : Set (Set S)) : Set (Set S) :=
  (boundaryDrawing Γ Z₁).E ∪ (boundaryDrawing Γ Z₂).E ∪ (boundaryDrawing Γ Z₃).E

/-- A counterexample to (5.4) "chosen with `N(Z₁, Z₂, Z₃)` minimal". -/
structure IsMinTriple [T1Space S] (Γ : Drawing S) (ins : Drawing S → Set S) (k : ℕ) (Ω : Set S)
    (ω : ℕ) (Z₁ Z₂ Z₃ : Set (Set S)) : Prop where
  triple : IsTriple Γ ins k Ω ω Z₁ Z₂ Z₃
  min : ∀ Z₁' Z₂' Z₃', IsTriple Γ ins k Ω ω Z₁' Z₂' Z₃' →
    (tripleE Γ Z₁ Z₂ Z₃).ncard ≤ (tripleE Γ Z₁' Z₂' Z₃').ncard

section Basic

variable [T1Space S] {Z₁ Z₂ Z₃ : Set (Set S)}

theorem IsTriple.swap₂₃ (h : IsTriple Γ ins k Ω ω Z₁ Z₂ Z₃) : IsTriple Γ ins k Ω ω Z₁ Z₃ Z₂ :=
  ⟨by rw [← h.cover, union_right_comm], h.d₁₃, h.d₁₂, h.d₂₃.symm, h.s₁, h.s₃, h.s₂⟩

theorem IsTriple.swap₁₂ (h : IsTriple Γ ins k Ω ω Z₁ Z₂ Z₃) : IsTriple Γ ins k Ω ω Z₂ Z₁ Z₃ :=
  ⟨by rw [← h.cover, union_comm Z₂], h.d₁₂.symm, h.d₂₃, h.d₁₃, h.s₂, h.s₁, h.s₃⟩

theorem tripleE_swap₂₃ : tripleE Γ Z₁ Z₃ Z₂ = tripleE Γ Z₁ Z₂ Z₃ := by
  unfold tripleE
  rw [union_right_comm]

theorem tripleE_swap₁₂ : tripleE Γ Z₂ Z₁ Z₃ = tripleE Γ Z₁ Z₂ Z₃ := by
  unfold tripleE
  rw [union_comm (boundaryDrawing Γ Z₂).E]

theorem IsMinTriple.swap₂₃ (h : IsMinTriple Γ ins k Ω ω Z₁ Z₂ Z₃) :
    IsMinTriple Γ ins k Ω ω Z₁ Z₃ Z₂ :=
  ⟨h.triple.swap₂₃, fun _ _ _ h' => by rw [tripleE_swap₂₃]; exact h.min _ _ _ h'⟩

theorem IsMinTriple.swap₁₂ (h : IsMinTriple Γ ins k Ω ω Z₁ Z₂ Z₃) :
    IsMinTriple Γ ins k Ω ω Z₂ Z₁ Z₃ :=
  ⟨h.triple.swap₁₂, fun _ _ _ h' => by rw [tripleE_swap₁₂]; exact h.min _ _ _ h'⟩

end Basic

/-- The vertices of `C` other than `v₁` whose outer regions all lie in `Z`: the set `W_i` of the
paper. -/
def outerSet (Γ : Drawing S) (X : Set S) (V : Set S) (v₁ : S) (Z : Set (Set S)) : Set S :=
  {v | v ∈ V ∧ v ≠ v₁ ∧ ∀ r ∈ Γ.R, v ∈ closure r → ¬ r ⊆ X → r ∈ Z}

/-- All regions at an edge are the two given ones. -/
theorem sides_of_edge (hS : IsClosedSurface S)
    {e a b r : Set S} (he : e ∈ Γ.E) (ha : a ∈ Γ.R) (hb : b ∈ Γ.R)
    (hne : a ≠ b) (ia : e ⊆ closure a) (ib : e ⊆ closure b) (hr : r ∈ Γ.R)
    (ir : (e ∩ closure r).Nonempty) : r = a ∨ r = b := by
  have hr' := edge_subset_closure_of_incident hS he hr ir
  rcases region_incident_two hS he ha hb hr ia ib hr' with h | h | h
  · exact absurd h hne
  · exact Or.inl h.symm
  · exact Or.inr h.symm

section Leaf

variable [T2Space S] (hS : IsClosedSurface S)
  (hs : IsSlope Γ k ins) (hw : IsWeighting Γ k Ω ω)
  {Z₁ : Set (Set S)} {C₁ : Drawing S} {v₁ : S} (hsm : IsSmall Γ ins k Ω ω Z₁)
  (hL : IsLeafRing ins (boundaryDrawing Γ Z₁) C₁ v₁)
include hS hs hw hsm hL

/-- Statement (2) of the proof of (5.4) (Graph Minors XI, page 83): "If $e \in E(C_1)$ then one
region of $\Gamma$ incident with $e$ belongs to $A \cap Z_1$ and
the other belongs to $B \cap (Z_2 \cup Z_3)$." -/
theorem leaf_edge_sides {e : Set S} (he : e ∈ C₁.E) :
    ∃ a b, a ∈ Γ.R ∧ b ∈ Γ.R ∧ a ⊆ ins C₁ ∧ ¬ b ⊆ ins C₁ ∧ a ∈ Z₁ ∧ b ∉ Z₁ ∧ e ⊆ closure a ∧
      e ⊆ closure b ∧ ∀ r ∈ Γ.R, (e ∩ closure r).Nonempty → r = a ∨ r = b := by
  have hsub : (boundaryDrawing Γ Z₁).IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hconf := boundaryDrawing_isConfined hw hsm.1
  obtain ⟨hC, hCs, hmax⟩ := hL.1
  have hCΓ := hCs.trans hsub
  have heΓ := hCΓ.2 he
  obtain ⟨⟨a, ha, hea, hai⟩, b, hb, heb, hbn⟩ :=
    exists_regions_of_circuit_edge hS hs hC hCΓ (hconf C₁ hC hCs) he
  have hne : a ≠ b := fun h => hbn (h ▸ hai)
  obtain ⟨x, hx⟩ := he.1
  have hsides := fun r (hr : r ∈ Γ.R) (ir : (e ∩ closure r).Nonempty) =>
    sides_of_edge hS heΓ ha hb hne hea heb hr ir
  have hbZ : b ∉ Z₁ := fun h =>
    theorem_4_3_ii hs hsub hconf hC hCs hmax he ⟨x, hx, heb hx⟩ hbn (hsm.2 b h)
  obtain ⟨⟨r, hrZ, hir⟩, -⟩ := mem_boundaryDrawing_E.mp (hCs.2 he)
  have haZ : a ∈ Z₁ := by
    rcases hsides r hir.2.1 hir.2.2 with rfl | rfl
    · exact hrZ
    · exact absurd hrZ hbZ
  exact ⟨a, b, ha, hb, hai, hbn, haZ, hbZ, hea, heb, hsides⟩

/-- The paper's "It follows from (2) that $R(v) \subseteq Z_2 \cup Z_3$ for all $v \ne v_1$" (Graph
Minors XI, page
83). Going around `v` from an edge of `C₁`, the region can leave `B - Z₁` only over an edge of
`N(Z₁)` not
in `ins(C₁)`, and at `v` there is none. -/
theorem leaf_vertex_regions {v : S} (hv : v ∈ C₁.V) (hne : v ≠ v₁) {r : Set S} (hr : r ∈ Γ.R)
    (hvr : v ∈ closure r) (hnot : ¬ r ⊆ ins C₁) : r ∉ Z₁ := by
  have hsub : (boundaryDrawing Γ Z₁).IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hconf := boundaryDrawing_isConfined hw hsm.1
  have hCs := hL.1.2.1
  have hC := hL.1.1
  have hCΓ := hCs.trans hsub
  have hl := hconf C₁ hC hCs
  have : Nonempty S := ⟨v⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  have hvΓ : v ∈ Γ.V := hCΓ.1 hv
  obtain ⟨g, hg, hvg⟩ := exists_edge_at_vertex hC hv
  have hgΓ := hCΓ.2 hg
  obtain ⟨c, hc⟩ := exists_end_eq hγ hgΓ hvΓ hvg
  have hfinH := finite_halfEdges Γ γ v
  have h2 : 2 ≤ Nat.card (halfEdges Γ γ v) := by
    have he := even_nHalf hS Γ hγ hvΓ Z₁
    have hsubH : nHalf (boundaryDrawing Γ Z₁) γ v ⊆ halfEdges Γ γ v :=
      fun x hx => ⟨hsub.2 hx.1, hx.2⟩
    have hmem : (g, c) ∈ nHalf (boundaryDrawing Γ Z₁) γ v := ⟨hCs.2 hg, hc⟩
    have hpos := (ncard_pos (hfinH.subset hsubH)).mpr ⟨_, hmem⟩
    have hle := ncard_le_ncard hsubH hfinH
    rw [Nat.card_coe_set_eq]
    obtain ⟨m, hm⟩ := he
    omega
  obtain ⟨next, ρ, hρ⟩ := exists_corners hS Γ hγ hvΓ h2
  have : Finite (halfEdges Γ γ v) := hfinH.to_subtype
  have hsurj := Finite.injective_iff_surjective.mp hρ.inj
  have hcl := (ins_facts_of_length hs hC hCΓ hl).1
  let P : halfEdges Γ γ v → Prop := fun k => ¬ ρ k ⊆ ins C₁ → ρ k ∉ Z₁
  -- Over an edge of `C₁`, the region is `A ∩ Z₁` or `B - Z₁`.
  have hedge : ∀ k, (next k).1.1 ∈ C₁.E → P (next k) := by
    intro k hk hnotk
    obtain ⟨a, b, -, -, hai, -, -, hbZ, -, -, hsides⟩ := leaf_edge_sides hS hs hw hsm hL hk
    obtain ⟨x, hx⟩ := hk.1
    rcases hsides _ (hρ.region _) ⟨x, hx, hρ.right k hx⟩ with h | h
    · exact absurd (h ▸ hai) hnotk
    · exact h ▸ hbZ
  have hstep : ∀ k, P k → P (next k) := by
    intro k hk
    by_cases heC : (next k).1.1 ∈ C₁.E
    · exact hedge k heC
    intro hnotk hZk
    have heΓ : (next k).1.1 ∈ Γ.E := (next k).2.1
    have hend : v ∈ closure (next k).1.1 := by
      have h := end_mem_closure hγ heΓ (next k).1.2
      have hev : γ (next k).1.1 (endOf (next k).1.2) = v := (next k).2.2
      rwa [hev] at h
    obtain ⟨x, hx⟩ := heΓ.1
    have hxU : x ∉ C₁.U := disjoint_left.mp (edge_disjoint_U hCΓ heΓ heC) hx
    -- The edge is outside `ins(C₁)`, since the next region is.
    have hxi : x ∉ ins C₁ := fun h => hnotk
      (region_subset_ins_of_closure hs hC hCΓ hl (hρ.region _) (hρ.right k hx) h hxU)
    -- So it is not an edge of `N(Z₁)`, as `v ≠ v₁`.
    have heN : (next k).1.1 ∉ (boundaryDrawing Γ Z₁).E := fun h =>
      hxi (hL.2.2 v hv hne _ h hend hx)
    have hkZ : ρ k ∈ Z₁ := by
      by_contra hkZ
      exact heN (mem_boundaryDrawing_E.mpr ⟨⟨_, hZk, heΓ, hρ.region _, x, hx, hρ.right k hx⟩, _,
        ⟨hρ.region _, hkZ⟩, heΓ, hρ.region _, x, hx, hρ.left k hx⟩)
    have hkin : ρ k ⊆ ins C₁ := by
      by_contra h
      exact hk h hkZ
    exact hxi (hcl.closure_subset_iff.mpr hkin (hρ.left k hx))
  let x₀ : halfEdges Γ γ v := ⟨(g, c), hgΓ, hc⟩
  obtain ⟨k₀, hk₀⟩ := hsurj x₀
  have hbase : P x₀ := by
    have h := hedge k₀ (by rw [hk₀]; exact hg)
    rwa [hk₀] at h
  have hall : ∀ k, P k := by
    intro k
    induction hρ.reach x₀ k with
    | refl => exact hbase
    | tail _ hyz ih => exact hyz ▸ hstep _ ih
  obtain ⟨k, rfl⟩ := hρ.all r hr hvr
  exact hall k hnot

/-- Regions on both sides of `ins(C₁)` at a vertex put it on `C₁`. -/
theorem vertex_of_both_sides {v : S} (hv : v ∈ Γ.V) {a b : Set S} (ha : a ∈ Γ.R) (hb : b ∈ Γ.R)
    (hai : a ⊆ ins C₁) (hbn : ¬ b ⊆ ins C₁) (hva : v ∈ closure a) (hvb : v ∈ closure b) :
    v ∈ C₁.V := by
  have hsub : (boundaryDrawing Γ Z₁).IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hconf := boundaryDrawing_isConfined hw hsm.1
  have hCΓ := hL.1.2.1.trans hsub
  have hNA := boundaryDrawing_inside hS hs hL.1.1 hCΓ (hconf C₁ hL.1.1 hL.1.2.1)
  have hm : v ∈ (boundaryDrawing Γ (insideRegions Γ (ins C₁))).V :=
    (mem_boundaryDrawing_V hS).mpr ⟨⟨a, ⟨ha, hai⟩, hv, Or.inr ha, hva⟩, b,
      ⟨hb, fun h => hbn h.2⟩, hv, Or.inr hb, hvb⟩
  rwa [hNA] at hm

/-- Statement (4), first part (Graph Minors XI, page 83): `N(Z - A)` lies in `N(Z)`. -/
theorem boundary_diff_inside {Z : Set (Set S)} (hZ : Z = Z₁ ∨ Disjoint Z Z₁) (hZR : Z ⊆ Γ.R) :
    (boundaryDrawing Γ (Z \ insideRegions Γ (ins C₁))).IsSubdrawing (boundaryDrawing Γ Z) := by
  have hsub : (boundaryDrawing Γ Z₁).IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hconf := boundaryDrawing_isConfined hw hsm.1
  have hCs := hL.1.2.1
  have hCΓ := hCs.trans hsub
  have hNA := boundaryDrawing_inside hS hs hL.1.1 hCΓ (hconf C₁ hL.1.1 hCs)
  constructor
  · intro v hv
    obtain ⟨⟨r, ⟨hrZ, hrA⟩, hir⟩, s, ⟨hsR, hsn⟩, his⟩ := (mem_boundaryDrawing_V hS).mp hv
    by_cases hsZ : s ∈ Z
    · have hsA : s ∈ insideRegions Γ (ins C₁) := by
        by_contra h
        exact hsn ⟨hsZ, h⟩
      have hvC : v ∈ C₁.V := vertex_of_both_sides hS hs hw hsm hL hir.1 hsR (hZR hrZ) hsA.2
        (fun h => hrA ⟨hZR hrZ, h⟩) his.2.2 hir.2.2
      rcases hZ with rfl | hd
      · exact hCs.1 hvC
      · obtain ⟨g, hg, hvg⟩ := exists_edge_at_vertex hL.1.1 hvC
        obtain ⟨a, b, ha, -, -, -, haZ, -, hga, -, -⟩ := leaf_edge_sides hS hs hw hsm hL hg
        exact (mem_boundaryDrawing_V hS).mpr ⟨⟨r, hrZ, hir⟩, a,
          ⟨ha, fun h => disjoint_left.mp hd h haZ⟩, hir.1, Or.inr ha,
          closure_minimal hga isClosed_closure hvg⟩
    · exact (mem_boundaryDrawing_V hS).mpr ⟨⟨r, hrZ, hir⟩, s, ⟨hsR, hsZ⟩, his⟩
  · intro e he
    obtain ⟨⟨r, ⟨hrZ, hrA⟩, hir⟩, s, ⟨hsR, hsn⟩, his⟩ := mem_boundaryDrawing_E.mp he
    by_cases hsZ : s ∈ Z
    · have hsA : s ∈ insideRegions Γ (ins C₁) := by
        by_contra h
        exact hsn ⟨hsZ, h⟩
      have heC : e ∈ C₁.E := by
        have hm : e ∈ (boundaryDrawing Γ (insideRegions Γ (ins C₁))).E :=
          mem_boundaryDrawing_E.mpr ⟨⟨s, hsA, his⟩, r, ⟨hZR hrZ, hrA⟩, hir⟩
        rwa [hNA] at hm
      rcases hZ with rfl | hd
      · exact hCs.2 heC
      · obtain ⟨a, b, ha, -, -, -, haZ, -, hga, -, -⟩ := leaf_edge_sides hS hs hw hsm hL heC
        obtain ⟨x, hx⟩ := heC.1
        exact mem_boundaryDrawing_E.mpr ⟨⟨r, hrZ, hir⟩, a,
          ⟨ha, fun h => disjoint_left.mp hd h haZ⟩, hir.1, ha, x, hx, hga hx⟩
    · exact mem_boundaryDrawing_E.mpr ⟨⟨r, hrZ, hir⟩, s, ⟨hsR, hsZ⟩, his⟩

/-- Statement (4), second part: `Z - A` is small. -/
theorem small_diff_inside [ConnectedSpace S] {Z : Set (Set S)} (hZ : Z = Z₁ ∨ Disjoint Z Z₁)
  (hZR : Z ⊆ Γ.R)
    (hZs : IsSmall Γ ins k Ω ω Z) : IsSmall Γ ins k Ω ω (Z \ insideRegions Γ (ins C₁)) := by
  refine theorem_5_3_proof hS hs hw hZR hZs sdiff_subset (lt_of_le_of_lt ?_ hZs.1)
  refine ncard_le_ncard (inter_subset_inter_right _ ?_)
    ((boundaryDrawing Γ Z).finite_V.subset inter_subset_right)
  exact (boundary_diff_inside hS hs hw hsm hL hZ hZR).1

/-- Statement (5) of the proof of (5.4) (Graph Minors XI, page 84). -/
theorem count_five {Z₂ Z₃ : Set (Set S)} (hR : Z₁ ∪ Z₂ ∪ Z₃ = Γ.R) (h₁₂ : Disjoint Z₁ Z₂)
    (hcount : (Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Z₃).ncard +
        (Ω ∩ ({v₁} \ (boundaryDrawing Γ Z₂).V)).ncard ≤
      (Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Z₂).ncard) :
    (Ω ∩ (boundaryDrawing Γ (Z₂ ∪ insideRegions Γ (ins C₁))).V).ncard ≤
      (Ω ∩ (boundaryDrawing Γ Z₂).V).ncard := by
  set W₂ := outerSet Γ (ins C₁) C₁.V v₁ Z₂ with hW₂
  set W₃ := outerSet Γ (ins C₁) C₁.V v₁ Z₃ with hW₃
  set X := (boundaryDrawing Γ Z₂).V with hX
  set Y := (boundaryDrawing Γ (Z₂ ∪ insideRegions Γ (ins C₁))).V with hY
  have hmemX := fun v => mem_boundaryDrawing_V (Γ := Γ) (Z := Z₂) (v := v) hS
  have hmemY := fun v => mem_boundaryDrawing_V (Γ := Γ)
    (Z := Z₂ ∪ insideRegions Γ (ins C₁)) (v := v) hS
  have hCΓ : C₁.IsSubdrawing Γ := hL.1.2.1.trans (Drawing.span_isSubdrawing Γ _ _)
  -- `W₂ ⊆ X - Y`.
  have hW₂X : W₂ ⊆ X := by
    rintro v ⟨hv, -, hall⟩
    obtain ⟨g, hg, hvg⟩ := exists_edge_at_vertex hL.1.1 hv
    obtain ⟨a, b, ha, hb, -, hbn, haZ, -, hga, hgb, -⟩ := leaf_edge_sides hS hs hw hsm hL hg
    have hvb := closure_minimal hgb isClosed_closure hvg
    have hva := closure_minimal hga isClosed_closure hvg
    exact (hmemX v).mpr ⟨⟨b, hall b hb hvb hbn, hCΓ.1 hv, Or.inr hb, hvb⟩, a,
      ⟨ha, fun h => disjoint_left.mp h₁₂ haZ h⟩, hCΓ.1 hv, Or.inr ha, hva⟩
  have hW₂Y : ∀ v ∈ W₂, v ∉ Y := by
    rintro v ⟨-, -, hall⟩ hvY
    obtain ⟨-, s, ⟨hsR, hsn⟩, his⟩ := (hmemY v).mp hvY
    have hsA : ¬ s ⊆ ins C₁ := fun h => hsn (Or.inr ⟨hsR, h⟩)
    exact hsn (Or.inl (hall s hsR his.2.2 hsA))
  -- `Y - X ⊆ W₃ ∪ D`.
  have hYX : ∀ v ∈ Y, v ∉ X → v ∈ W₃ ∨ v ∈ ({v₁} \ X : Set S) := by
    intro v hvY hvX
    obtain ⟨⟨r, hr, hir⟩, s, ⟨hsR, hsn⟩, his⟩ := (hmemY v).mp hvY
    have hsZ₂ : s ∉ Z₂ := fun h => hsn (Or.inl h)
    have hsA : ¬ s ⊆ ins C₁ := fun h => hsn (Or.inr ⟨hsR, h⟩)
    have hrA : r ∈ insideRegions Γ (ins C₁) := by
      rcases hr with h | h
      · exact absurd ((hmemX v).mpr ⟨⟨r, h, hir⟩, s, ⟨hsR, hsZ₂⟩, his⟩) hvX
      · exact h
    have hvC : v ∈ C₁.V := vertex_of_both_sides hS hs hw hsm hL hir.1 hrA.1 hsR hrA.2 hsA
      hir.2.2 his.2.2
    by_cases hvv : v = v₁
    · exact Or.inr ⟨hvv, hvX⟩
    refine Or.inl ⟨hvC, hvv, fun t ht hvt hnt => ?_⟩
    have hnZ₁ := leaf_vertex_regions hS hs hw hsm hL hvC hvv ht hvt hnt
    rw [← hR] at ht
    rcases ht with (h | h) | h
    · exact absurd h hnZ₁
    · exact absurd ((hmemX v).mpr ⟨⟨t, h, hir.1, Or.inr (hR ▸ Or.inl (Or.inr h)), hvt⟩, s,
        ⟨hsR, hsZ₂⟩, his⟩) hvX
    · exact h
  have hXf : X.Finite := (boundaryDrawing Γ Z₂).finite_V
  have hW₂f : W₂.Finite := hXf.subset hW₂X
  have hW₃f : W₃.Finite := C₁.finite_V.subset fun v hv => hv.1
  have hcover : Ω ∩ Y ⊆ ((Ω ∩ X) \ (Ω ∩ W₂)) ∪ (Ω ∩ W₃) ∪ (Ω ∩ ({v₁} \ X)) := by
    rintro v ⟨hvΩ, hvY⟩
    by_cases hvX : v ∈ X
    · exact Or.inl (Or.inl ⟨⟨hvΩ, hvX⟩, fun h => hW₂Y v h.2 hvY⟩)
    · rcases hYX v hvY hvX with h | h
      · exact Or.inl (Or.inr ⟨hvΩ, h⟩)
      · exact Or.inr ⟨hvΩ, h⟩
  have hdf : ((Ω ∩ X) \ (Ω ∩ W₂)).Finite := (hXf.subset inter_subset_right).sdiff
  have hsf : (Ω ∩ W₃).Finite := hW₃f.subset inter_subset_right
  have htf : (Ω ∩ ({v₁} \ X)).Finite :=
    ((finite_singleton v₁).subset sdiff_subset).subset inter_subset_right
  have h₁ := ncard_le_ncard hcover ((hdf.union hsf).union htf)
  have h₂ := ncard_union_le (((Ω ∩ X) \ (Ω ∩ W₂)) ∪ (Ω ∩ W₃)) (Ω ∩ ({v₁} \ X))
  have h₃ := ncard_union_le ((Ω ∩ X) \ (Ω ∩ W₂)) (Ω ∩ W₃)
  have h₄ := ncard_sdiff_add_ncard_of_subset (inter_subset_inter_right Ω hW₂X)
    (hXf.subset inter_subset_right)
  omega

end Leaf

section Main

variable [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
  (hs : IsSlope Γ k ins) (hw : IsWeighting Γ k Ω ω)
  {Z₁ Z₂ Z₃ : Set (Set S)} {C₁ : Drawing S} {v₁ : S}
include hS hs hw

/-- Statement (6) of the proof of (5.4), under the choice that the paper makes "from the symmetry"
(Graph Minors XI, page 84). -/
theorem leaf_aux (hmin : IsMinTriple Γ ins k Ω ω Z₁ Z₂ Z₃)
    (hL : IsLeafRing ins (boundaryDrawing Γ Z₁) C₁ v₁)
    (h₃ : (C₁.E ∩ (boundaryDrawing Γ Z₂).E).Nonempty)
    (hcount : (Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Z₃).ncard +
        (Ω ∩ ({v₁} \ (boundaryDrawing Γ Z₂).V)).ncard ≤
      (Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Z₂).ncard) :
    insideRegions Γ (ins C₁) ⊆ Z₁ ∧
      (boundaryDrawing Γ Z₁).E ∩ (boundaryDrawing Γ Z₃).E ⊆ C₁.E := by
  obtain ⟨⟨hcov, d₁₂, d₁₃, d₂₃, s₁, s₂, s₃⟩, hmn⟩ := id hmin
  have ht := hmin.triple
  set A := insideRegions Γ (ins C₁) with hA
  have hR₁ : Z₁ ⊆ Γ.R := fun r h => hcov ▸ Or.inl (Or.inl h)
  have hR₂ : Z₂ ⊆ Γ.R := fun r h => hcov ▸ Or.inl (Or.inr h)
  have hR₃ : Z₃ ⊆ Γ.R := fun r h => hcov ▸ Or.inr h
  have hRA : A ⊆ Γ.R := fun r h => h.1
  have hsub : (boundaryDrawing Γ Z₁).IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hconf := boundaryDrawing_isConfined hw s₁.1
  have hCs := hL.1.2.1
  have hC := hL.1.1
  have hCΓ := hCs.trans hsub
  have hl := hconf C₁ hC hCs
  have hNA : boundaryDrawing Γ A = C₁ := boundaryDrawing_inside hS hs hC hCΓ hl
  have hEA : ∀ e, e ∈ (boundaryDrawing Γ A).E ↔ e ∈ C₁.E := fun e => by rw [hNA]
  have hsame := @leaf_edge_sides S _ Γ k ω ins Ω _ hS hs hw Z₁ C₁ v₁ s₁ hL
  have hsmall₁ := small_diff_inside hS hs hw s₁ hL (Or.inl rfl) hR₁ s₁
  have hsmall₂ := small_diff_inside hS hs hw s₁ hL (Or.inr d₁₂.symm) hR₂ s₂
  have hsmall₃ := small_diff_inside hS hs hw s₁ hL (Or.inr d₁₃.symm) hR₃ s₃
  have hsub₁ := boundary_diff_inside hS hs hw s₁ hL (Or.inl rfl) hR₁
  have hsub₂ := boundary_diff_inside hS hs hw s₁ hL (Or.inr d₁₂.symm) hR₂
  have hsub₃ := boundary_diff_inside hS hs hw s₁ hL (Or.inr d₁₃.symm) hR₃
  -- The edges of `N(Z₂ ∪ A)` lie in `N(Z₂) ∪ C₁`.
  have hY : ∀ e ∈ (boundaryDrawing Γ (Z₂ ∪ A)).E, e ∈ (boundaryDrawing Γ Z₂).E ∨ e ∈ C₁.E := by
    intro e he
    obtain ⟨⟨r, hr, hir⟩, s, ⟨hsR, hsn⟩, his⟩ := mem_boundaryDrawing_E.mp he
    rcases hr with h | h
    · exact Or.inl (mem_boundaryDrawing_E.mpr ⟨⟨r, h, hir⟩, s, ⟨hsR, fun h' => hsn
      (Or.inl h')⟩, his⟩)
    · exact Or.inr ((hEA e).mp (mem_boundaryDrawing_E.mpr
        ⟨⟨r, h, hir⟩, s, ⟨hsR, fun h' => hsn (Or.inr h')⟩, his⟩))
  have hfinE : (tripleE Γ Z₁ Z₂ Z₃).Finite :=
    ((boundaryDrawing Γ Z₁).finite_edges.union (boundaryDrawing Γ Z₂).finite_edges).union
      (boundaryDrawing Γ Z₃).finite_edges
  have hCK : ∀ e ∈ C₁.E, e ∈ tripleE Γ Z₁ Z₂ Z₃ := fun e he => Or.inl (Or.inl (hCs.2 he))
  have hN₂K : ∀ e ∈ (boundaryDrawing Γ Z₂).E, e ∈ tripleE Γ Z₁ Z₂ Z₃ :=
    fun e he => Or.inl (Or.inr he)
  have hYK : ∀ e ∈ (boundaryDrawing Γ (Z₂ ∪ A)).E, e ∈ tripleE Γ Z₁ Z₂ Z₃ := fun e he =>
    (hY e he).elim (hN₂K e) (hCK e)
  -- By the choice of `(Z₁, Z₂, Z₃)`, the set `Z₂ ∪ A` is not small.
  have hnotsmall : ¬ IsSmall Γ ins k Ω ω (Z₂ ∪ A) := by
    intro hsmall
    have hT : IsTriple Γ ins k Ω ω (Z₁ \ A) (Z₂ ∪ A) (Z₃ \ A) := by
      refine ⟨?_, ?_, ?_, ?_, hsmall₁, hsmall, hsmall₃⟩
      · ext r
        rw [← hcov]
        constructor
        · rintro ((⟨h, -⟩ | h | h) | ⟨h, -⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact hcov ▸ h.1
          · exact Or.inr h
        · intro h
          by_cases hrA : r ∈ A
          · exact Or.inl (Or.inr (Or.inr hrA))
          · rcases h with (h | h) | h
            · exact Or.inl (Or.inl ⟨h, hrA⟩)
            · exact Or.inl (Or.inr (Or.inl h))
            · exact Or.inr ⟨h, hrA⟩
      · refine disjoint_left.mpr ?_
        rintro r ⟨h, hrA⟩ (h' | h')
        · exact disjoint_left.mp d₁₂ h h'
        · exact hrA h'
      · exact disjoint_left.mpr fun r h h' => disjoint_left.mp d₁₃ h.1 h'.1
      · refine disjoint_left.mpr ?_
        rintro r (h' | h') ⟨h, hrA⟩
        · exact disjoint_left.mp d₂₃ h' h
        · exact hrA h'
    have hle := hmn _ _ _ hT
    have hsubK : tripleE Γ (Z₁ \ A) (Z₂ ∪ A) (Z₃ \ A) ⊆ tripleE Γ Z₁ Z₂ Z₃ := by
      rintro e ((he | he) | he)
      · exact Or.inl (Or.inl (hsub₁.2 he))
      · exact hYK e he
      · exact Or.inr (hsub₃.2 he)
    obtain ⟨e₀, he₀C, he₀N⟩ := h₃
    obtain ⟨a, b, ha, hb, hai, hbn, haZ, hbZ, hea, heb, hsides⟩ := hsame he₀C
    obtain ⟨⟨r, hrZ, hir⟩, -⟩ := mem_boundaryDrawing_E.mp he₀N
    have hbZ₂ : b ∈ Z₂ := by
      rcases hsides r hir.2.1 hir.2.2 with rfl | rfl
      · exact absurd haZ (disjoint_right.mp d₁₂ hrZ)
      · exact hrZ
    have haA : a ∈ A := ⟨ha, hai⟩
    have hbA : b ∉ A := fun h => hbn h.2
    have hnotK : e₀ ∉ tripleE Γ (Z₁ \ A) (Z₂ ∪ A) (Z₃ \ A) := by
      rintro ((he | he) | he)
      · obtain ⟨⟨r', hr', hir'⟩, -⟩ := mem_boundaryDrawing_E.mp he
        rcases hsides r' hir'.2.1 hir'.2.2 with rfl | rfl
        · exact hr'.2 haA
        · exact hbZ hr'.1
      · obtain ⟨-, r', ⟨hr'R, hr'n⟩, hir'⟩ := mem_boundaryDrawing_E.mp he
        rcases hsides r' hir'.2.1 hir'.2.2 with rfl | rfl
        · exact hr'n (Or.inr haA)
        · exact hr'n (Or.inl hbZ₂)
      · obtain ⟨⟨r', hr', hir'⟩, -⟩ := mem_boundaryDrawing_E.mp he
        rcases hsides r' hir'.2.1 hir'.2.2 with rfl | rfl
        · exact hr'.2 haA
        · exact disjoint_left.mp d₂₃ hbZ₂ hr'.1
    have hlt := ncard_lt_ncard (⟨hsubK, fun h => hnotK (h (hCK e₀ he₀C))⟩ :
      tripleE Γ (Z₁ \ A) (Z₂ ∪ A) (Z₃ \ A) ⊂ tripleE Γ Z₁ Z₂ Z₃) hfinE
    omega
  -- By (5) and (5.2), the rest `R(Γ) - (Z₂ ∪ A)` is small.
  have hltY : (Ω ∩ (boundaryDrawing Γ (Z₂ ∪ A)).V).ncard < ω :=
    lt_of_le_of_lt (count_five hS hs hw s₁ hL hcov d₁₂ hcount) s₂.1
  have hRY : Z₂ ∪ A ⊆ Γ.R := union_subset hR₂ hRA
  have hrest : IsSmall Γ ins k Ω ω (Γ.R \ (Z₂ ∪ A)) :=
    (theorem_5_2_proof hS hs hw hRY hltY).1.resolve_left hnotsmall
  have hAsmall : IsSmall Γ ins k Ω ω A := by
    constructor
    · rw [hNA]
      refine lt_of_le_of_lt (ncard_le_ncard (inter_subset_inter_right _ hCs.1)
        ((boundaryDrawing Γ Z₁).finite_V.subset inter_subset_right)) s₁.1
    · intro r hr
      rw [hNA]
      exact ⟨C₁, hC, Drawing.IsSubdrawing.refl _, hl, hr.2⟩
  have hT₂ : IsTriple Γ ins k Ω ω A (Z₂ \ A) (Γ.R \ (Z₂ ∪ A)) := by
    refine ⟨?_, ?_, ?_, ?_, hAsmall, hsmall₂, hrest⟩
    · ext r
      constructor
      · rintro ((h | h) | h)
        · exact h.1
        · exact hR₂ h.1
        · exact h.1
      · intro h
        by_cases hrA : r ∈ A
        · exact Or.inl (Or.inl hrA)
        · by_cases hrZ : r ∈ Z₂
          · exact Or.inl (Or.inr ⟨hrZ, hrA⟩)
          · exact Or.inr ⟨h, fun h' => h'.elim hrZ hrA⟩
    · exact disjoint_left.mpr fun r h h' => h'.2 h
    · exact disjoint_left.mpr fun r h h' => h'.2 (Or.inr h)
    · exact disjoint_left.mpr fun r h h' => h'.2 (Or.inl h.1)
  have hcompl : boundaryDrawing Γ (Γ.R \ (Z₂ ∪ A)) = boundaryDrawing Γ (Z₂ ∪ A) :=
    boundaryDrawing_compl hRY
  have hsubT : tripleE Γ A (Z₂ \ A) (Γ.R \ (Z₂ ∪ A)) ⊆ tripleE Γ Z₁ Z₂ Z₃ := by
    rintro e ((he | he) | he)
    · exact hCK e ((hEA e).mp he)
    · exact hN₂K e (hsub₂.2 he)
    · rw [hcompl] at he
      exact hYK e he
  have heqT : tripleE Γ A (Z₂ \ A) (Γ.R \ (Z₂ ∪ A)) = tripleE Γ Z₁ Z₂ Z₃ :=
    eq_of_subset_of_ncard_le hsubT (hmn _ _ _ hT₂) hfinE
  -- An edge of `K` outside `C₁` has a side in `Z₂ - A`.
  have hcases' : ∀ e ∈ tripleE Γ Z₁ Z₂ Z₃, e ∉ C₁.E →
      ∃ r ∈ Z₂, r ∉ A ∧ Γ.EdgeRegionIncident e r := by
    intro e he heC
    rw [← heqT] at he
    rcases he with (he | he) | he
    · exact absurd ((hEA e).mp he) heC
    · obtain ⟨⟨r, hr, hir⟩, -⟩ := mem_boundaryDrawing_E.mp he
      exact ⟨r, hr.1, hr.2, hir⟩
    · rw [hcompl] at he
      obtain ⟨⟨r, hr, hir⟩, s, ⟨hsR, hsn⟩, his⟩ := mem_boundaryDrawing_E.mp he
      have hrA : r ∉ A := fun hrA => heC ((hEA e).mp (mem_boundaryDrawing_E.mpr
        ⟨⟨r, hrA, hir⟩, s, ⟨hsR, fun h' => hsn (Or.inr h')⟩, his⟩))
      exact ⟨r, hr.resolve_right hrA, hrA, hir⟩
  constructor
  · -- `A ⊆ Z₁` by (5.1).
    intro s hsA
    by_contra hsZ
    obtain ⟨e₁, he₁⟩ := IsCircuit.E_nonempty hC
    obtain ⟨a, -, ha, -, hai, -, haZ, -, -, -, -⟩ := hsame he₁
    have hnonU : ∀ r ∈ Γ.R, r ⊆ ins C₁ → r ⊆ ins C₁ \ C₁.U := fun r hr hin x hx =>
      ⟨hin hx, fun hU => region_subset hr hx (hCΓ.U_subset hU)⟩
    obtain ⟨x, hx⟩ := region_nonempty ha
    have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
    have hD : ins C₁ \ C₁.U ∈ C₁.R :=
      inner_mem_R hS hs hC hCΓ hl (hnonU a ha hai hx).1 (hnonU a ha hai hx).2
    obtain ⟨e, heΓ, heC, a', b', ha'Z, hb'Z, ha'D, hb'D, hia', hib'⟩ := theorem_5_1_proof hS hCΓ hD
      ha
      haZ hsA.1 hsZ (hnonU a ha hai) (hnonU s hsA.1 hsA.2)
    have ha'A : a' ∈ A := ⟨hia'.2.1, fun y hy => (ha'D hy).1⟩
    have hb'A : b' ∈ A := ⟨hib'.2.1, fun y hy => (hb'D hy).1⟩
    have heN : e ∈ tripleE Γ Z₁ Z₂ Z₃ := Or.inl (Or.inl (mem_boundaryDrawing_E.mpr
      ⟨⟨a', ha'Z, hia'⟩, b', ⟨hib'.2.1, hb'Z⟩, hib'⟩))
    obtain ⟨r, hrZ, hrA, hir⟩ := hcases' e heN heC
    have hne : a' ≠ b' := fun h => hb'Z (h ▸ ha'Z)
    rcases sides_of_edge hS heΓ hia'.2.1 hib'.2.1 hne
        (edge_subset_closure_of_incident hS heΓ hia'.2.1 hia'.2.2)
        (edge_subset_closure_of_incident hS heΓ hib'.2.1 hib'.2.2) hir.2.1 hir.2.2 with h | h
    · exact hrA (h ▸ ha'A)
    · exact hrA (h ▸ hb'A)
  · -- The first claim of (6).
    rintro e ⟨he₁, he₃⟩
    by_contra heC
    obtain ⟨r, hrZ, -, hir⟩ := hcases' e (Or.inl (Or.inl he₁)) heC
    obtain ⟨⟨a, haZ, hia⟩, -⟩ := mem_boundaryDrawing_E.mp he₁
    obtain ⟨⟨b, hbZ, hib⟩, -⟩ := mem_boundaryDrawing_E.mp he₃
    have hne : a ≠ b := fun h => disjoint_left.mp d₁₃ haZ (h ▸ hbZ)
    rcases sides_of_edge hS hia.1 hia.2.1 hib.2.1 hne
        (edge_subset_closure_of_incident hS hia.1 hia.2.1 hia.2.2)
        (edge_subset_closure_of_incident hS hia.1 hib.2.1 hib.2.2) hir.2.1 hir.2.2 with h | h
    · exact disjoint_left.mp d₁₂ haZ (h ▸ hrZ)
    · exact disjoint_left.mp d₂₃ hrZ (h ▸ hbZ)

/-- Statement (6) of the proof of (5.4) for a ring as in (1), with the choice made "from the
symmetry"
left open (Graph Minors XI, page 84). -/
theorem leaf_main (hmin : IsMinTriple Γ ins k Ω ω Z₁ Z₂ Z₃)
    (hL : IsLeafRing ins (boundaryDrawing Γ Z₁) C₁ v₁) :
    insideRegions Γ (ins C₁) ⊆ Z₁ ∧ ∃ Zp Zq : Set (Set S), ((Zp = Z₂ ∧ Zq = Z₃) ∨ (Zp = Z₃ ∧ Zq
      = Z₂)) ∧
      (C₁.E ∩ (boundaryDrawing Γ Zp).E).Nonempty ∧
      (boundaryDrawing Γ Z₁).E ∩ (boundaryDrawing Γ Zq).E ⊆ C₁.E := by
  obtain ⟨hcov, d₁₂, d₁₃, d₂₃, s₁, s₂, s₃⟩ := hmin.triple
  have hsame := @leaf_edge_sides S _ Γ k ω ins Ω _ hS hs hw Z₁ C₁ v₁ s₁ hL
  obtain ⟨f, hf, hv₁f⟩ := exists_edge_at_vertex hL.1.1 hL.2.1
  have hCΓ : C₁.IsSubdrawing Γ := hL.1.2.1.trans (Drawing.span_isSubdrawing Γ _ _)
  -- The conditions of `leaf_aux` follow from the comparison of `|W₂ ∩ Ω|` and `|W₃ ∩ Ω|`.
  have horder : ∀ Y₂ Y₃ : Set (Set S), Disjoint Z₁ Y₂ →
      ((Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Y₃).ncard < (Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Y₂).ncard ∨
        ((Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Y₃).ncard = (Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Y₂).ncard ∧
          f ∈ (boundaryDrawing Γ Y₂).E)) →
      (C₁.E ∩ (boundaryDrawing Γ Y₂).E).Nonempty ∧
      (Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Y₃).ncard + (Ω ∩ ({v₁} \ (boundaryDrawing Γ Y₂).V)).ncard ≤
        (Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Y₂).ncard := by
    intro Y₂ Y₃ hd h
    rcases h with h | ⟨h, hfY⟩
    · constructor
      · have hne : (Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Y₂).Nonempty := by
          by_contra hemp
          rw [not_nonempty_iff_eq_empty] at hemp
          rw [hemp, ncard_empty] at h
          omega
        obtain ⟨v, -, hv, -, hall⟩ := hne
        obtain ⟨g, hg, hvg⟩ := exists_edge_at_vertex hL.1.1 hv
        obtain ⟨a, b, ha, hb, -, hbn, haZ, -, hga, hgb, -⟩ := hsame hg
        obtain ⟨x, hx⟩ := hg.1
        have hbY := hall b hb (closure_minimal hgb isClosed_closure hvg) hbn
        have hgΓ := hCΓ.2 hg
        exact ⟨g, hg, mem_boundaryDrawing_E.mpr ⟨⟨b, hbY, hgΓ, hb, x, hx, hgb hx⟩, a,
          ⟨ha, disjoint_left.mp hd haZ⟩, hgΓ, ha, x, hx, hga hx⟩⟩
      · have hD : (Ω ∩ ({v₁} \ (boundaryDrawing Γ Y₂).V)).ncard ≤ 1 := by
          have hsub : Ω ∩ ({v₁} \ (boundaryDrawing Γ Y₂).V) ⊆ {v₁} := fun _ hx => hx.2.1
          calc _ ≤ ({v₁} : Set S).ncard := ncard_le_ncard hsub (finite_singleton _)
            _ = 1 := ncard_singleton _
        omega
    · refine ⟨⟨f, hf, hfY⟩, ?_⟩
      have hv₁Y : v₁ ∈ (boundaryDrawing Γ Y₂).V := by
        have hm : v₁ ∈ closure f ∩ Γ.V := ⟨hv₁f, hCΓ.1 hL.2.1⟩
        rw [← (Drawing.span_isSubdrawing Γ _ _).closure_inter_V hfY] at hm
        exact hm.2
      have hemp : Ω ∩ ({v₁} \ (boundaryDrawing Γ Y₂).V) = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff, mem_empty_iff_false, iff_false]
        rintro ⟨-, rfl, h'⟩
        exact h' hv₁Y
      rw [hemp, ncard_empty]
      omega
  have hfN : f ∈ (boundaryDrawing Γ Z₂).E ∨ f ∈ (boundaryDrawing Γ Z₃).E := by
    obtain ⟨a, b, ha, hb, -, -, haZ, hbZ, hfa, hfb, -⟩ := hsame hf
    obtain ⟨x, hx⟩ := hf.1
    have hfΓ := hCΓ.2 hf
    have hbR : b ∈ Z₁ ∪ Z₂ ∪ Z₃ := hcov ▸ hb
    rcases hbR with (h | h) | h
    · exact absurd h hbZ
    · exact Or.inl (mem_boundaryDrawing_E.mpr ⟨⟨b, h, hfΓ, hb, x, hx, hfb hx⟩, a,
        ⟨ha, disjoint_left.mp d₁₂ haZ⟩, hfΓ, ha, x, hx, hfa hx⟩)
    · exact Or.inr (mem_boundaryDrawing_E.mpr ⟨⟨b, h, hfΓ, hb, x, hx, hfb hx⟩, a,
        ⟨ha, disjoint_left.mp d₁₃ haZ⟩, hfΓ, ha, x, hx, hfa hx⟩)
  have h₂₃ : (Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Z₃).ncard < (Ω ∩ outerSet Γ
    (ins C₁) C₁.V v₁ Z₂).ncard ∨
      ((Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Z₃).ncard = (Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Z₂).ncard ∧
        f ∈ (boundaryDrawing Γ Z₂).E) →
      insideRegions Γ (ins C₁) ⊆ Z₁ ∧ ∃ Zp Zq : Set (Set S), ((Zp = Z₂ ∧ Zq = Z₃) ∨ (Zp = Z₃ ∧ Zq
        = Z₂)) ∧
      (C₁.E ∩ (boundaryDrawing Γ Zp).E).Nonempty ∧
      (boundaryDrawing Γ Z₁).E ∩ (boundaryDrawing Γ Zq).E ⊆ C₁.E := fun h => by
    obtain ⟨h₁, h₂⟩ := horder Z₂ Z₃ d₁₂ h
    obtain ⟨h₃, h₄⟩ := leaf_aux hS hs hw hmin hL h₁ h₂
    exact ⟨h₃, Z₂, Z₃, Or.inl ⟨rfl, rfl⟩, h₁, h₄⟩
  have h₃₂ : (Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Z₂).ncard < (Ω ∩ outerSet Γ
    (ins C₁) C₁.V v₁ Z₃).ncard ∨
      ((Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Z₂).ncard = (Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Z₃).ncard ∧
        f ∈ (boundaryDrawing Γ Z₃).E) →
      insideRegions Γ (ins C₁) ⊆ Z₁ ∧ ∃ Zp Zq : Set (Set S), ((Zp = Z₂ ∧ Zq = Z₃) ∨ (Zp = Z₃ ∧ Zq
        = Z₂)) ∧
      (C₁.E ∩ (boundaryDrawing Γ Zp).E).Nonempty ∧
      (boundaryDrawing Γ Z₁).E ∩ (boundaryDrawing Γ Zq).E ⊆ C₁.E := fun h => by
    obtain ⟨h₁, h₂⟩ := horder Z₃ Z₂ d₁₃ h
    obtain ⟨h₃, h₄⟩ := leaf_aux hS hs hw hmin.swap₂₃ hL h₁ h₂
    exact ⟨h₃, Z₃, Z₂, Or.inr ⟨rfl, rfl⟩, h₁, h₄⟩
  rcases lt_trichotomy (Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Z₃).ncard
    (Ω ∩ outerSet Γ (ins C₁) C₁.V v₁ Z₂).ncard with h | h | h
  · exact h₂₃ (Or.inl h)
  · rcases hfN with hf' | hf'
    · exact h₂₃ (Or.inr ⟨h, hf'⟩)
    · exact h₃₂ (Or.inr ⟨h.symm, hf'⟩)
  · exact h₃₂ (Or.inl h)

/-- The end of statement (7): if `N(Z₁)` and `N(Z₃)` have no common edge, then `N(Z₂)` captures
every
region of `Γ`, contrary to (4.4), which here takes the form of (5.2). -/
theorem no_empty_pair (ht : IsTriple Γ ins k Ω ω Z₁ Z₂ Z₃)
    (hemp : Disjoint (boundaryDrawing Γ Z₁).E (boundaryDrawing Γ Z₃).E) : False := by
  obtain ⟨hcov, d₁₂, d₁₃, d₂₃, s₁, s₂, s₃⟩ := ht
  have hR₁ : Z₁ ⊆ Γ.R := fun r h => hcov ▸ Or.inl (Or.inl h)
  have hR₂ : Z₂ ⊆ Γ.R := fun r h => hcov ▸ Or.inl (Or.inr h)
  have hR₃ : Z₃ ⊆ Γ.R := fun r h => hcov ▸ Or.inr h
  have hsplit : ∀ r ∈ Γ.R, r ∈ Z₁ ∨ r ∈ Z₂ ∨ r ∈ Z₃ := fun r hr => by
    have hm : r ∈ Z₁ ∪ Z₂ ∪ Z₃ := hcov ▸ hr
    rcases hm with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hE₁ : (boundaryDrawing Γ Z₁).E ⊆ (boundaryDrawing Γ Z₂).E := by
    intro e he
    obtain ⟨⟨r, hr, hir⟩, s, ⟨hsR, hsn⟩, his⟩ := mem_boundaryDrawing_E.mp he
    rcases hsplit s hsR with h | h | h
    · exact absurd h hsn
    · exact mem_boundaryDrawing_E.mpr ⟨⟨s, h, his⟩, r, ⟨hR₁ hr, disjoint_left.mp d₁₂ hr⟩, hir⟩
    · exact absurd (mem_boundaryDrawing_E.mpr ⟨⟨s, h, his⟩, r,
        ⟨hR₁ hr, disjoint_left.mp d₁₃ hr⟩, hir⟩) (disjoint_left.mp hemp he)
  have hE₃ : (boundaryDrawing Γ Z₃).E ⊆ (boundaryDrawing Γ Z₂).E := by
    intro e he
    obtain ⟨⟨r, hr, hir⟩, s, ⟨hsR, hsn⟩, his⟩ := mem_boundaryDrawing_E.mp he
    rcases hsplit s hsR with h | h | h
    · exact absurd he (disjoint_left.mp hemp (mem_boundaryDrawing_E.mpr ⟨⟨s, h, his⟩, r,
        ⟨hR₃ hr, disjoint_right.mp d₁₃ hr⟩, hir⟩))
    · exact mem_boundaryDrawing_E.mpr ⟨⟨s, h, his⟩, r, ⟨hR₃ hr, disjoint_right.mp d₂₃ hr⟩, hir⟩
    · exact absurd h hsn
  have hN₂ : (boundaryDrawing Γ Z₂).IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hcap : ∀ {Y : Set (Set S)}, (boundaryDrawing Γ Y).E ⊆ (boundaryDrawing Γ Z₂).E →
      IsSmall Γ ins k Ω ω Y → ∀ r ∈ Y, Captures ins k (boundaryDrawing Γ Z₂) r := by
    rintro Y hE hY r hr
    obtain ⟨C, hC, hCs, hl, hin⟩ := hY.2 r hr
    exact ⟨C, hC, circuit_isSubdrawing_of_E hC (hCs.trans (Drawing.span_isSubdrawing Γ _ _)) hN₂
      (hCs.2.trans hE), hl, hin⟩
  have hcompl : boundaryDrawing Γ (Γ.R \ Z₂) = boundaryDrawing Γ Z₂ := boundaryDrawing_compl hR₂
  refine (theorem_5_2_proof hS hs hw hR₂ s₂.1).2 ⟨s₂, ?_, ?_⟩
  · rw [hcompl]
    exact s₂.1
  · rintro r ⟨hr, hrn⟩
    rw [hcompl]
    rcases hsplit r hr with h | h | h
    · exact hcap hE₁ s₁ r h
    · exact absurd h hrn
    · exact hcap hE₃ s₃ r h

omit [ConnectedSpace S] hs hw in
/-- Every edge of `N(Z)` lies on a circuit of `N(Z)` (Graph Minors XI, page 83: "every vertex of
$N(Z_1)$ has even valency and so every edge of $N(Z_1)$ is in a circuit"). -/
theorem exists_circuit_N (Z : Set (Set S)) :
    ∀ e ∈ (boundaryDrawing Γ Z).E, ∃ D : Drawing S, D.IsCircuit ∧
      D.IsSubdrawing (boundaryDrawing Γ Z) ∧ e ∈ D.E := by
  intro e he
  have : Nonempty S := (he.1.mono (he.2.1.trans sdiff_subset)).to_subtype.map fun x => x.1
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  exact exists_circuit_of_even hγ (Drawing.span_isSubdrawing Γ _ _)
    (fun v hv => even_nHalf hS Γ hγ hv Z) he

/-- Statement (7) of the proof of (5.4) (Graph Minors XI, page 84): "`Z₁ = A`". -/
theorem leaf_all_inside (hmin : IsMinTriple Γ ins k Ω ω Z₁ Z₂ Z₃)
    (hL : IsLeafRing ins (boundaryDrawing Γ Z₁) C₁ v₁) : Z₁ = insideRegions Γ (ins C₁) := by
  obtain ⟨hcov, d₁₂, d₁₃, d₂₃, s₁, s₂, s₃⟩ := id hmin.triple
  have hR₁ : Z₁ ⊆ Γ.R := fun r h => hcov ▸ Or.inl (Or.inl h)
  have hconf := boundaryDrawing_isConfined hw s₁.1
  have hs' := theorem_4_2_proof hs (Drawing.span_isSubdrawing Γ _ _ :
    (boundaryDrawing Γ Z₁).IsSubdrawing Γ)
  refine subset_antisymm (fun s hs₁ => ?_) (leaf_main hS hs hw hmin hL).1
  refine ⟨hR₁ hs₁, ?_⟩
  by_contra hsn
  -- There is another ring, and so a second ring as in (1).
  obtain ⟨D, hD, hDs, -, hin⟩ := s₁.2 s hs₁
  obtain ⟨C', hC', hle⟩ := exists_ring_above ins hD hDs
  have hne : C' ≠ C₁ := fun h => hsn (h ▸ hin.trans hle)
  obtain ⟨C₂, v₂, hL₂, hne₂⟩ := exists_second_leaf_ring hs' hconf
    (exists_circuit_N hS Z₁) hL hC' hne
  obtain ⟨-, Zp, Zq, hpq, ⟨g, hg₁, hgp⟩, hq⟩ := leaf_main hS hs hw hmin hL
  obtain ⟨-, Zp', Zq', hpq', -, hq'⟩ := leaf_main hS hs hw hmin hL₂
  -- Distinct rings have no common edge.
  have hdisj : Disjoint C₁.E C₂.E := ring_edge_disjoint hs' hconf hL.1 hL₂.1 hne₂
  have hg₁N : g ∈ (boundaryDrawing Γ Z₁).E := hL.1.2.1.2 hg₁
  -- The partner of `C₂` is not the partner `Zp` of `C₁`, so it is `Zq`.
  have hpartner : Zq' = Zq := by
    by_contra hneq
    have hZq' : Zq' = Zp := by
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hpq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        first | rfl | exact absurd rfl hneq
    exact disjoint_left.mp hdisj hg₁ (hq' ⟨hg₁N, hZq' ▸ hgp⟩)
  have hempty : Disjoint (boundaryDrawing Γ Z₁).E (boundaryDrawing Γ Zq).E :=
    disjoint_left.mpr fun e h₁ h₃ =>
      disjoint_left.mp hdisj (hq ⟨h₁, h₃⟩) (hq' ⟨h₁, hpartner ▸ h₃⟩)
  rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact no_empty_pair hS hs hw hmin.triple hempty
  · exact no_empty_pair hS hs hw hmin.triple.swap₂₃ hempty

/-- `Z₁` is not empty (Graph Minors XI, page 82: "$Z_1 \ne \emptyset$ because otherwise a
contradiction would be obtained by taking $Z = Z_2$
in (5.2)"). -/
theorem IsTriple.nonempty₁ (ht : IsTriple Γ ins k Ω ω Z₁ Z₂ Z₃) : Z₁.Nonempty := by
  by_contra hemp
  rw [not_nonempty_iff_eq_empty] at hemp
  obtain ⟨hcov, -, -, d₂₃, -, s₂, s₃⟩ := ht
  subst hemp
  rw [empty_union] at hcov
  have hR₂ : Z₂ ⊆ Γ.R := fun r h => hcov ▸ Or.inl h
  have heq : Γ.R \ Z₂ = Z₃ := by
    rw [← hcov, union_sdiff_left]
    exact d₂₃.symm.sdiff_eq_left
  refine (theorem_5_2_proof hS hs hw hR₂ s₂.1).2 ⟨s₂, ?_⟩
  rw [heq]
  exact s₃

/-- Statements (7) and (8) of the proof of (5.4) (Graph Minors XI, pages 84–85): `N(Z₁)` is a
circuit,
of length `< 2θ`, and `Z₁` is the set of regions in its `ins`. -/
theorem exists_circuit_of_min (hmin : IsMinTriple Γ ins k Ω ω Z₁ Z₂ Z₃) :
    (boundaryDrawing Γ Z₁).IsCircuit ∧ (boundaryDrawing Γ Z₁).length < k ∧
      Z₁ = insideRegions Γ (ins (boundaryDrawing Γ Z₁)) := by
  have ht := hmin.triple
  have hconf := boundaryDrawing_isConfined hw ht.s₁.1
  have hsub : (boundaryDrawing Γ Z₁).IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hs' := theorem_4_2_proof hs hsub
  obtain ⟨r, hr⟩ := ht.nonempty₁ hS hs hw
  obtain ⟨D, hD, hDs, -, -⟩ := ht.s₁.2 r hr
  obtain ⟨C, v, hL⟩ := exists_leaf_ring hs' hconf (exists_circuit_N hS Z₁) hD hDs
  have hZ := leaf_all_inside hS hs hw hmin hL
  have hCΓ := hL.1.2.1.trans hsub
  have hl := hconf C hL.1.1 hL.1.2.1
  have hNA := boundaryDrawing_inside hS hs hL.1.1 hCΓ hl
  rw [← hZ] at hNA
  rw [hNA]
  exact ⟨hL.1.1, hl, hZ⟩

omit [ConnectedSpace S] hw in
/-- The regions in `ins(C)` lie all in or all out of `ins(T)`, if `U(T)` misses the interior of
`ins(C)`. -/
theorem inside_same_side {C T : Drawing S} (hC : C.IsCircuit) (hCs : C.IsSubdrawing Γ)
    (hl : C.length < k) (hT : T.IsCircuit) (hTs : T.IsSubdrawing Γ) (hTl : T.length < k)
    (hoff : ∀ e ∈ T.E, ∃ r ∈ Γ.R, e ⊆ closure r ∧ ¬ r ⊆ ins C) :
    insideRegions Γ (ins C) ⊆ insideRegions Γ (ins T) ∨
      Disjoint (insideRegions Γ (ins C)) (insideRegions Γ (ins T)) := by
  obtain ⟨hclT, hfrT, -⟩ := ins_facts_of_length hs hT hTs hTl
  have hdis : Disjoint (ins C \ C.U) (frontier (ins T)) := by
    rw [hfrT]
    refine disjoint_left.mpr fun x hx hxU => ?_
    obtain ⟨g, hg, hxg⟩ : ∃ g ∈ T.E, x ∈ closure g := by
      rw [T.U_eq] at hxU
      rcases hxU with h | h
      · exact exists_edge_at_vertex hT h
      · obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h
        exact ⟨g, hg, hxg⟩
    obtain ⟨r, hr, hgr, hnot⟩ := hoff g hg
    exact hnot (region_subset_ins_of_closure hs hC hCs hl hr
      (closure_minimal hgr isClosed_closure hxg) hx.1 hx.2)
  have hnonU : ∀ r ∈ insideRegions Γ (ins C), r ⊆ ins C \ C.U := fun r hr x hx =>
    ⟨hr.2 hx, fun hU => region_subset hr.1 hx (hCs.U_subset hU)⟩
  rcases subset_or_disjoint_of_frontier hclT (isPreconnected_inner hS hs hC hCs hl) hdis with h | h
  · exact Or.inl fun r hr => ⟨hr.1, (hnonU r hr).trans h⟩
  · refine Or.inr (disjoint_left.mpr fun r hr hr' => ?_)
    obtain ⟨x, hx⟩ := region_nonempty hr.1
    exact disjoint_left.mp h (hnonU r hr hx) (hr'.2 hx)

end Main

/-- A subset of a union of three disjoint sets, with each in it or disjoint from it, that is neither
empty nor everything, is one of them or the complement of one of them. -/
theorem sets_cases {α : Type*} {R Z₁ Z₂ Z₃ Y : Set α} (hc : Z₁ ∪ Z₂ ∪ Z₃ = R) (hY : Y ⊆ R)
    (h₁ : Z₁ ⊆ Y ∨ Disjoint Z₁ Y) (h₂ : Z₂ ⊆ Y ∨ Disjoint Z₂ Y) (h₃ : Z₃ ⊆ Y ∨ Disjoint Z₃ Y)
    (hne : Y.Nonempty) (hne' : (R \ Y).Nonempty) :
    (Y = Z₁ ∨ Y = Z₂ ∨ Y = Z₃) ∨ (R \ Y = Z₁ ∨ R \ Y = Z₂ ∨ R \ Y = Z₃) := by
  have hcov : ∀ r ∈ R, r ∈ Z₁ ∨ r ∈ Z₂ ∨ r ∈ Z₃ := fun r hr => by
    have hm : r ∈ Z₁ ∪ Z₂ ∪ Z₃ := hc ▸ hr
    rcases hm with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hsub₁ : Z₁ ⊆ R := fun r h => hc ▸ Or.inl (Or.inl h)
  have hsub₂ : Z₂ ⊆ R := fun r h => hc ▸ Or.inl (Or.inr h)
  have hsub₃ : Z₃ ⊆ R := fun r h => hc ▸ Or.inr h
  have hone : ∀ {A B C : Set α}, (∀ r ∈ R, r ∈ A ∨ r ∈ B ∨ r ∈ C) → A ⊆ Y → Disjoint B Y →
      Disjoint C Y → Y = A := fun hcv hA hB hC => subset_antisymm (fun r hr =>
    ((hcv r (hY hr)).resolve_right fun h => h.elim (fun h' => disjoint_left.mp hB h' hr)
      fun h' => disjoint_left.mp hC h' hr)) hA
  have htwo : ∀ {A B C : Set α}, (∀ r ∈ R, r ∈ A ∨ r ∈ B ∨ r ∈ C) → C ⊆ R → A ⊆ Y → B ⊆ Y →
      Disjoint C Y → R \ Y = C := fun hcv hCR hA hB hC => subset_antisymm (fun r hr => by
    rcases hcv r hr.1 with h | h | h
    · exact absurd (hA h) hr.2
    · exact absurd (hB h) hr.2
    · exact h) fun r hr => ⟨hCR hr, disjoint_left.mp hC hr⟩
  have hc₂₁₃ : ∀ r ∈ R, r ∈ Z₂ ∨ r ∈ Z₁ ∨ r ∈ Z₃ := fun r hr => by
    rcases hcov r hr with h | h | h <;> simp [h]
  have hc₃₁₂ : ∀ r ∈ R, r ∈ Z₃ ∨ r ∈ Z₁ ∨ r ∈ Z₂ := fun r hr => by
    rcases hcov r hr with h | h | h <;> simp [h]
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rcases h₃ with h₃ | h₃
  · obtain ⟨r, hr, hrn⟩ := hne'
    rcases hcov r hr with h | h | h
    · exact absurd (h₁ h) hrn
    · exact absurd (h₂ h) hrn
    · exact absurd (h₃ h) hrn
  · exact Or.inr (Or.inr (Or.inr (htwo hcov hsub₃ h₁ h₂ h₃)))
  · exact Or.inr (Or.inr (Or.inl (htwo (A := Z₁) (B := Z₃) (fun r hr => by
      rcases hcov r hr with h | h | h <;> simp [h]) hsub₂ h₁ h₃ h₂)))
  · exact Or.inl (Or.inl (hone hcov h₁ h₂ h₃))
  · exact Or.inr (Or.inl (htwo (A := Z₂) (B := Z₃) (fun r hr => by
      rcases hcov r hr with h | h | h <;> simp [h]) hsub₁ h₂ h₃ h₁))
  · exact Or.inl (Or.inr (Or.inl (hone hc₂₁₃ h₂ h₁ h₃)))
  · exact Or.inl (Or.inr (Or.inr (hone hc₃₁₂ h₃ h₁ h₂)))
  · obtain ⟨r, hr⟩ := hne
    rcases hcov r (hY hr) with h | h | h
    · exact absurd hr (disjoint_left.mp h₁ h)
    · exact absurd hr (disjoint_left.mp h₂ h)
    · exact absurd hr (disjoint_left.mp h₃ h)

section Partition

variable [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
  {Z₁ Z₂ Z₃ : Set (Set S)}
include hS

omit [ConnectedSpace S] in
/-- Two parts of the partition: an edge in both of their `N` is not in the third. -/
theorem triple_not_three (ht : IsTriple Γ ins k Ω ω Z₁ Z₂ Z₃) {e : Set S}
    (h₁ : e ∈ (boundaryDrawing Γ Z₁).E) (h₂ : e ∈ (boundaryDrawing Γ Z₂).E) :
    e ∉ (boundaryDrawing Γ Z₃).E := by
  intro h₃
  obtain ⟨⟨a, ha, hia⟩, -⟩ := mem_boundaryDrawing_E.mp h₁
  obtain ⟨⟨b, hb, hib⟩, -⟩ := mem_boundaryDrawing_E.mp h₂
  obtain ⟨⟨c, hc, hic⟩, -⟩ := mem_boundaryDrawing_E.mp h₃
  have hne : a ≠ b := fun h => disjoint_left.mp ht.d₁₂ ha (h ▸ hb)
  rcases sides_of_edge hS hia.1 hia.2.1 hib.2.1 hne
      (edge_subset_closure_of_incident hS hia.1 hia.2.1 hia.2.2)
      (edge_subset_closure_of_incident hS hia.1 hib.2.1 hib.2.2) hic.2.1 hic.2.2 with h | h
  · exact disjoint_left.mp ht.d₁₃ ha (h ▸ hc)
  · exact disjoint_left.mp ht.d₂₃ hb (h ▸ hc)

omit [ConnectedSpace S] hS in
/-- An edge of `N(Z₁)` not in `N(Z₂)` is in `N(Z₃)`. -/
theorem triple_third (ht : IsTriple Γ ins k Ω ω Z₁ Z₂ Z₃) {e : Set S}
    (h₁ : e ∈ (boundaryDrawing Γ Z₁).E) (h₂ : e ∉ (boundaryDrawing Γ Z₂).E) :
    e ∈ (boundaryDrawing Γ Z₃).E := by
  obtain ⟨⟨a, ha, hia⟩, s, ⟨hsR, hsn⟩, his⟩ := mem_boundaryDrawing_E.mp h₁
  have hm : s ∈ Z₁ ∪ Z₂ ∪ Z₃ := ht.cover ▸ hsR
  rcases hm with (h | h) | h
  · exact absurd h hsn
  · exact absurd (mem_boundaryDrawing_E.mpr ⟨⟨s, h, his⟩, a,
      ⟨hia.2.1, disjoint_left.mp ht.d₁₂ ha⟩, hia⟩) h₂
  · exact mem_boundaryDrawing_E.mpr ⟨⟨s, h, his⟩, a, ⟨hia.2.1, disjoint_left.mp ht.d₁₃ ha⟩, hia⟩

/-- There is no counterexample to (5.4) with `N(Z₁, Z₂, Z₃)` minimal. -/
theorem no_min_triple (hs : IsSlope Γ k ins) (hw : IsWeighting Γ k Ω ω)
    (hmin : IsMinTriple Γ ins k Ω ω Z₁ Z₂ Z₃) : False := by
  have ht := hmin.triple
  obtain ⟨hc₁, hl₁, hZ₁⟩ := exists_circuit_of_min hS hs hw hmin
  obtain ⟨hc₂, hl₂, hZ₂⟩ := exists_circuit_of_min hS hs hw hmin.swap₁₂
  obtain ⟨hc₃, hl₃, hZ₃⟩ := exists_circuit_of_min hS hs hw hmin.swap₂₃.swap₁₂
  have sub : ∀ Z : Set (Set S), (boundaryDrawing Γ Z).IsSubdrawing Γ := fun Z =>
    Drawing.span_isSubdrawing Γ _ _
  have ht₂₁₃ := ht.swap₁₂
  have ht₃₁₂ := ht.swap₂₃.swap₁₂
  have ht₃₂₁ : IsTriple Γ ins k Ω ω Z₃ Z₂ Z₁ := ht₃₁₂.swap₂₃
  have hE : ∀ e, e ∈ (boundaryDrawing Γ Z₃).E ↔
      (e ∈ (boundaryDrawing Γ Z₁).E ∧ e ∉ (boundaryDrawing Γ Z₂).E) ∨
      (e ∉ (boundaryDrawing Γ Z₁).E ∧ e ∈ (boundaryDrawing Γ Z₂).E) := by
    intro e
    constructor
    · intro h
      by_cases h₁ : e ∈ (boundaryDrawing Γ Z₁).E
      · exact Or.inl ⟨h₁, fun h₂ => triple_not_three hS ht h₁ h₂ h⟩
      · exact Or.inr ⟨h₁, by
          by_contra h₂
          exact h₁ (triple_third ht₃₂₁ h h₂)⟩
    · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
      · exact triple_third ht h₁ h₂
      · exact triple_third ht₂₁₃ h₂ h₁
  have hnot : ∃ e ∈ (boundaryDrawing Γ Z₁).E, e ∉ (boundaryDrawing Γ Z₂).E := by
    by_contra hno
    push Not at hno
    have heq := circuit_E_eq_of_subset hc₂ hc₁ (sub Z₂) (sub Z₁) hno
    obtain ⟨e, he⟩ := IsCircuit.E_nonempty hc₃
    rcases (hE e).mp he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact h₂ (heq ▸ h₁)
    · exact h₁ (heq ▸ h₂)
  have hoffN : ∀ {X Z : Set (Set S)}, (X = Z ∨ Disjoint X Z) →
      Z = insideRegions Γ (ins (boundaryDrawing Γ Z)) → ∀ e ∈ (boundaryDrawing Γ X).E,
      ∃ r ∈ Γ.R, e ⊆ closure r ∧ ¬ r ⊆ ins (boundaryDrawing Γ Z) := by
    intro X Z hX hZ e he
    obtain ⟨⟨a, ha, hia⟩, s, ⟨hsR, hsn⟩, his⟩ := mem_boundaryDrawing_E.mp he
    rcases hX with rfl | hd
    · exact ⟨s, hsR, edge_subset_closure_of_incident hS his.1 hsR his.2.2, fun h =>
        hsn (hZ ▸ ⟨hsR, h⟩)⟩
    · exact ⟨a, hia.2.1, edge_subset_closure_of_incident hS hia.1 hia.2.1 hia.2.2, fun h =>
        disjoint_left.mp hd ha (hZ ▸ ⟨hia.2.1, h⟩)⟩
  have hshort : ∀ T : Drawing S, T.IsCircuit → T.IsSubdrawing Γ →
      (∀ e ∈ T.E, e ∈ (boundaryDrawing Γ Z₁).E ∨ e ∈ (boundaryDrawing Γ Z₂).E) → T.length < k →
      T.E = (boundaryDrawing Γ Z₁).E ∨ T.E = (boundaryDrawing Γ Z₂).E ∨
        T.E = (boundaryDrawing Γ Z₃).E := by
    intro T hT hTs hTE hTl
    have hNY : boundaryDrawing Γ (insideRegions Γ (ins T)) = T :=
      boundaryDrawing_inside hS hs hT hTs hTl
    have hYR : insideRegions Γ (ins T) ⊆ Γ.R := fun r h => h.1
    have hcompl := boundaryDrawing_compl hYR
    obtain ⟨e₀, he₀⟩ := IsCircuit.E_nonempty hT
    obtain ⟨⟨a, ha, -, hai⟩, b, hb, -, hbn⟩ :=
      exists_regions_of_circuit_edge hS hs hT hTs hTl he₀
    have hside : ∀ {Z : Set (Set S)}, (Z₁ = Z ∨ Disjoint Z₁ Z) → (Z₂ = Z ∨ Disjoint Z₂ Z) →
        (boundaryDrawing Γ Z).IsCircuit → (boundaryDrawing Γ Z).length < k →
        Z = insideRegions Γ (ins (boundaryDrawing Γ Z)) →
        Z ⊆ insideRegions Γ (ins T) ∨ Disjoint Z (insideRegions Γ (ins T)) := by
      intro Z h₁ h₂ hc hl hZ
      have := inside_same_side hS hs hc (sub Z) hl hT hTs hTl fun e he =>
        (hTE e he).elim (hoffN h₁ hZ e) (hoffN h₂ hZ e)
      rwa [← hZ] at this
    have s₁ := hside (Or.inl rfl) (Or.inr ht.d₁₂.symm) hc₁ hl₁ hZ₁
    have s₂ := hside (Or.inr ht.d₁₂) (Or.inl rfl) hc₂ hl₂ hZ₂
    have s₃ := hside (Or.inr ht.d₁₃) (Or.inr ht.d₂₃) hc₃ hl₃ hZ₃
    rcases sets_cases ht.cover hYR s₁ s₂ s₃ ⟨a, ha, hai⟩ ⟨b, hb, fun h => hbn h.2⟩ with
      (h | h | h) | (h | h | h)
    · exact Or.inl (by rw [← hNY, h])
    · exact Or.inr (Or.inl (by rw [← hNY, h]))
    · exact Or.inr (Or.inr (by rw [← hNY, h]))
    · exact Or.inl (by rw [← h, hcompl, hNY])
    · exact Or.inr (Or.inl (by rw [← h, hcompl, hNY]))
    · exact Or.inr (Or.inr (by rw [← h, hcompl, hNY]))
  obtain ⟨P₀, P₁, P₂, a, b, hP₀, hP₁, hP₂, sP₀, sP₁, sP₂, p₀, p₁, p₂, v₀₁, v₁₂, v₂₀, e₀₁, e₁₂, e₂₀,
    h₀₁, h₁₂, h₂₀⟩ := exists_theta hc₁ hc₂ hc₃ (sub Z₁) (sub Z₂) (sub Z₃) hl₁ hl₂ hE hnot hshort
  have hthree := hs.three_paths P₀ P₁ P₂ a b hP₀ hP₁ hP₂ sP₀ sP₁ sP₂ p₀ p₁ p₂ v₀₁ v₁₂ v₂₀ e₀₁ e₁₂
    e₂₀
    (h₁₂ ▸ hl₂) (h₂₀ ▸ hl₃) (h₀₁ ▸ hl₁)
  rw [h₀₁, h₁₂, h₂₀] at hthree
  have key : ∀ {Z Z' : Set (Set S)}, Z.Nonempty → Disjoint Z Z' →
      Z = insideRegions Γ (ins (boundaryDrawing Γ Z)) →
      Z' = insideRegions Γ (ins (boundaryDrawing Γ Z')) →
      ¬ ins (boundaryDrawing Γ Z) ⊆ ins (boundaryDrawing Γ Z') := by
    intro Z Z' ⟨r, hr⟩ hd hZ hZ' hsub
    have hrZ : r ∈ insideRegions Γ (ins (boundaryDrawing Γ Z)) := hZ ▸ hr
    have hrZ' : r ∈ insideRegions Γ (ins (boundaryDrawing Γ Z')) := ⟨hrZ.1, hrZ.2.trans hsub⟩
    exact disjoint_left.mp hd hr (hZ' ▸ hrZ')
  have n₁ := ht.nonempty₁ hS hs hw
  have n₂ := ht₂₁₃.nonempty₁ hS hs hw
  have n₃ := ht₃₁₂.nonempty₁ hS hs hw
  rcases hthree with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact key n₃ ht.d₂₃.symm hZ₃ hZ₂ h
  · exact key n₂ ht.d₂₃ hZ₂ hZ₃ h
  · exact key n₂ ht.d₁₂.symm hZ₂ hZ₁ h

/-- **(5.4)** of Graph Minors XI (page 82): "If $(Z_1, Z_2, Z_3)$ is a partition of $R(\Gamma)$,
then one of $Z_1, Z_2, Z_3$ is not
small." -/
theorem theorem_5_4_proof (hs : IsSlope Γ k ins) (hw : IsWeighting Γ k Ω ω) :
    PartitionNotSmall Γ ins k Ω ω := by
  classical
  intro Z₁ Z₂ Z₃ hc d₁₂ d₁₃ d₂₃ ⟨s₁, s₂, s₃⟩
  have hex : ∃ n, ∃ Y₁ Y₂ Y₃, IsTriple Γ ins k Ω ω Y₁ Y₂ Y₃ ∧ (tripleE Γ Y₁ Y₂ Y₃).ncard = n :=
    ⟨_, Z₁, Z₂, Z₃, ⟨hc, d₁₂, d₁₃, d₂₃, s₁, s₂, s₃⟩, rfl⟩
  obtain ⟨Y₁, Y₂, Y₃, hT, hn⟩ := Nat.find_spec hex
  refine no_min_triple hS hs hw (Z₁ := Y₁) (Z₂ := Y₂) (Z₃ := Y₃) ⟨hT, fun Y₁' Y₂' Y₃' hT' => ?_⟩
  rw [hn]
  exact Nat.find_min' hex ⟨Y₁', Y₂', Y₃', hT', rfl⟩

/-- **(5.5)** of Graph Minors XI (page 86): "If $Z_1, Z_2, Z_3 \subseteq R(\Gamma)$ are small, then
$Z_1 \cup Z_2 \cup Z_3 \ne
R(\Gamma)$." -/
theorem theorem_5_5_proof (hs : IsSlope Γ k ins) (hw : IsWeighting Γ k Ω ω)
    (h₁ : IsSmall Γ ins k Ω ω Z₁) (h₂ : IsSmall Γ ins k Ω ω Z₂) (h₃ : IsSmall Γ ins k Ω ω Z₃) :
    Z₁ ∪ Z₂ ∪ Z₃ ≠ Γ.R :=
  theorem_5_5_of_partition hS hs hw (theorem_5_4_proof hS hs hw) h₁ h₂ h₃

end Partition

end GraphMinor.GM11
