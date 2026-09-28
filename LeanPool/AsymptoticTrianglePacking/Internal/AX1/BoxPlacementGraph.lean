/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the **placement hypergraph** of the box-allocation residual

The residual `Nibble.AX1.BoxAllocationResidual` (`Nibble.BoxAllocationSpec`) asks for cell sets
`I c a ⊆ Fin P` of prescribed sizes `sz c a`, one per cluster of each copy, so that two copies
sharing a cluster pair occupy disjoint rectangles there.  This file builds the hypergraph whose
matchings *are* the partial allocations:

* the vertices are the cell-pair slots `(S, T, i, j)` of the cluster pairs (each unordered pair
  represented once, in the orientation of an injective indexing `idx` of the clusters) together
  with one token per copy (`Nibble.AX1.PlaceVtx`);
* the edges are the *placements* `Nibble.AX1.placeEdge`: a copy `c` together with a choice `A` of a
  cell set of the prescribed size in each of its three clusters occupies its token and the three
  rectangles `A a × A (a+1)`;
* the weight of a placement is `1/#placements of c`, so that each copy carries total weight `1`.

Two placements are disjoint exactly when they belong to different copies and their rectangles do
not overlap, so a matching is a partial allocation.  The three estimates the nibble needs are
proved here:

* `Nibble.AX1.BoxPlace.wLoad_inl_le` — the load of a slot of the cluster pair `(S, T)` is at most
  `boxDemand cl sz S T / P²`, i.e. at most `1 - ε` by the hypothesis of the residual, and the load
  of a token is exactly `1`;
* `Nibble.AX1.BoxPlace.codeg_inl_inl_le`, `codeg_inl_inr_le`, `codeg_inr_inr` — every weighted
  codegree is `O(s₀/P)`, which is where the small-box restriction `s₀ ≤ θ·P` enters: two placements
  overlapping in *two* prescribed slots are pinned down in one more coordinate, at a cost of a
  factor `s₀/P`;
* `Nibble.AX1.BoxPlace.sum_placeWt` — the total weight is the number of copies.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.BoxPlacementCount
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.BoxPlacementEdge
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.BoxAllocationSpec
public import LeanPool.AsymptoticTrianglePacking.Internal.WeightedBoundedEdges

/-! # Box placement hypergraph -/

@[expose] public section

open Finset

namespace Nibble.AX1

namespace BoxPlace

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {P : ℕ}
  {idx : ι → ℕ} {cl : κ → ZMod 3 → ι} {sz : κ → ZMod 3 → ℕ}

/-- The number of placements of the copy `c`. -/
def placeCard (P : ℕ) (sz : κ → ZMod 3 → ℕ) (c : κ) : ℕ := #(BoxCount.plc P (sz c))

/-- **The placement hypergraph**: all placements of all copies. -/
def placeFam (P : ℕ) (idx : ι → ℕ) (cl : κ → ZMod 3 → ι) (sz : κ → ZMod 3 → ℕ) :
    Finset (Finset (PlaceVtx ι κ P)) :=
  Finset.univ.biUnion (fun c : κ => (BoxCount.plc P (sz c)).image (placeEdge idx cl c))

/-- **The weight of a placement**: the reciprocal of the number of placements of its copy, so that
the placements of a copy carry total weight `1`. -/
noncomputable def placeWt (P : ℕ) (sz : κ → ZMod 3 → ℕ) : Finset (PlaceVtx ι κ P) → ℝ :=
  fun U => ∑ c : κ, if (Sum.inr c : PlaceVtx ι κ P) ∈ U then ((placeCard P sz c : ℝ))⁻¹ else 0

omit [Fintype ι] in
/-- The edges of the placement hypergraph are the placements. -/
theorem mem_placeFam {U : Finset (PlaceVtx ι κ P)} (hU : U ∈ placeFam P idx cl sz) :
    ∃ (c : κ) (A : ZMod 3 → Finset (Fin P)), A ∈ BoxCount.plc P (sz c) ∧
      U = placeEdge idx cl c A := by
  rw [placeFam, Finset.mem_biUnion] at hU
  obtain ⟨c, -, hU⟩ := hU
  rw [Finset.mem_image] at hU
  obtain ⟨A, hA, rfl⟩ := hU
  exact ⟨c, A, hA, rfl⟩


/-- The contribution of one copy to the demand of the cluster pair `(S, T)`. -/
def boxDemandC (cl : κ → ZMod 3 → ι) (sz : κ → ZMod 3 → ℕ) (c : κ) (S T : ι) : ℝ :=
  ∑ a : ZMod 3, ∑ b : ZMod 3, if cl c a = S ∧ cl c b = T then (sz c a : ℝ) * (sz c b : ℝ) else 0

omit [Fintype ι] [DecidableEq κ] in
theorem boxDemand_eq_sum (S T : ι) :
    boxDemand cl sz S T = ∑ c : κ, boxDemandC cl sz c S T := rfl

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem boxDemandC_nonneg (c : κ) (S T : ι) : 0 ≤ boxDemandC cl sz c S T := by
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  split
  · positivity
  · exact le_rfl

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem sz_mul_le_boxDemandC {c : κ} {p q : ZMod 3} {S T : ι} (hp : cl c p = S) (hq : cl c q = T) :
    (sz c p : ℝ) * (sz c q : ℝ) ≤ boxDemandC cl sz c S T := by
  have hterm : ∀ a : ZMod 3, 0 ≤ ∑ b : ZMod 3,
      if cl c a = S ∧ cl c b = T then (sz c a : ℝ) * (sz c b : ℝ) else 0 := by
    intro a
    refine Finset.sum_nonneg fun b _ => ?_
    split
    · positivity
    · exact le_rfl
  have h1 : (∑ b : ZMod 3, if cl c p = S ∧ cl c b = T then (sz c p : ℝ) * (sz c b : ℝ) else 0)
      ≤ boxDemandC cl sz c S T :=
    Finset.single_le_sum (f := fun a => ∑ b : ZMod 3,
      if cl c a = S ∧ cl c b = T then (sz c a : ℝ) * (sz c b : ℝ) else 0)
      (fun a _ => hterm a) (Finset.mem_univ p)
  have h2 : (sz c p : ℝ) * (sz c q : ℝ)
      ≤ ∑ b : ZMod 3, if cl c p = S ∧ cl c b = T then (sz c p : ℝ) * (sz c b : ℝ) else 0 := by
    have h3 : ∀ b : ZMod 3, 0 ≤
        (if cl c p = S ∧ cl c b = T then (sz c p : ℝ) * (sz c b : ℝ) else 0) := by
      intro b
      split
      · positivity
      · exact le_rfl
    calc (sz c p : ℝ) * (sz c q : ℝ)
        = (if cl c p = S ∧ cl c q = T then (sz c p : ℝ) * (sz c q : ℝ) else 0) :=
          (ite_eq_left ⟨hp, hq⟩).symm
      _ ≤ _ := Finset.single_le_sum (f := fun b : ZMod 3 =>
          if cl c p = S ∧ cl c b = T then (sz c p : ℝ) * (sz c b : ℝ) else 0)
          (fun b _ => h3 b) (Finset.mem_univ q)
  linarith

/-! ### Sums over the placement hypergraph -/

section Structure

variable (hidx : Function.Injective idx) (hcl : ∀ c, Function.Injective (cl c))
  (hsz1 : ∀ c a, 1 ≤ sz c a) (hszP : ∀ c a, sz c a ≤ P)

include hsz1 in
omit [Fintype κ] [DecidableEq κ] in
theorem plc_nonempty {c : κ} {A : ZMod 3 → Finset (Fin P)} (hA : A ∈ BoxCount.plc P (sz c))
    (a : ZMod 3) : (A a).Nonempty := by
  rw [← Finset.card_pos, BoxCount.mem_plc.mp hA a]
  exact hsz1 c a

include hidx hcl hsz1 in
omit [Fintype ι] in
/-- A sum over the placement hypergraph is a sum over copies and placements. -/
theorem sum_placeFam (f : Finset (PlaceVtx ι κ P) → ℝ) :
    ∑ U ∈ placeFam P idx cl sz, f U
      = ∑ c : κ, ∑ A ∈ BoxCount.plc P (sz c), f (placeEdge idx cl c A) := by
  classical
  have hpd : (↑(Finset.univ : Finset κ) : Set κ).PairwiseDisjoint
      (fun c : κ => (BoxCount.plc P (sz c)).image (placeEdge idx cl c)) := by
    intro c _ c' _ hcc
    rw [Function.onFun, Finset.disjoint_left]
    rintro U hU hU'
    rw [Finset.mem_image] at hU hU'
    obtain ⟨A, -, rfl⟩ := hU
    obtain ⟨A', -, hA'⟩ := hU'
    have hmem : (Sum.inr c : PlaceVtx ι κ P) ∈ placeEdge idx cl c A :=
      (mem_placeEdge_inr (A := A) (idx := idx) c).mpr rfl
    rw [← hA', mem_placeEdge_inr] at hmem
    exact hcc hmem
  rw [placeFam, Finset.sum_biUnion hpd]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_image fun A hA A' hA' h => ?_
  exact (placeEdge_inj hidx (hcl c) (hcl c) (plc_nonempty hsz1 hA) (plc_nonempty hsz1 hA') h).2

include hidx hcl hsz1 in
omit [Fintype ι] in
/-- A filtered sum over the placement hypergraph. -/
theorem sum_placeFam_filter (p : Finset (PlaceVtx ι κ P) → Prop) [DecidablePred p]
    (f : Finset (PlaceVtx ι κ P) → ℝ) :
    ∑ U ∈ (placeFam P idx cl sz).filter p, f U
      = ∑ c : κ, ∑ A ∈ (BoxCount.plc P (sz c)).filter (fun A => p (placeEdge idx cl c A)),
          f (placeEdge idx cl c A) := by
  classical
  rw [Finset.sum_filter, sum_placeFam hidx hcl hsz1]
  exact Finset.sum_congr rfl fun c _ => (Finset.sum_filter _ _).symm

omit [Fintype ι] in
/-- The weight of a placement of `c` is the reciprocal of the number of placements of `c`. -/
theorem placeWt_edge (c : κ) (A : ZMod 3 → Finset (Fin P)) :
    placeWt P sz (placeEdge idx cl c A) = ((placeCard P sz c : ℝ))⁻¹ := by
  classical
  simp only [placeWt, mem_placeEdge_inr]
  rw [Finset.sum_ite_eq' Finset.univ c (fun c' => ((placeCard P sz c' : ℝ))⁻¹)]
  simp

omit [Fintype ι] in
theorem placeWt_nonneg (U : Finset (PlaceVtx ι κ P)) : 0 ≤ placeWt P sz U := by
  refine Finset.sum_nonneg fun c _ => ?_
  split
  · positivity
  · exact le_rfl

include hszP in
omit [Fintype κ] [DecidableEq κ] in
theorem placeCard_pos (c : κ) : 0 < placeCard P sz c :=
  BoxCount.card_plc_pos (fun a => hszP c a)

include hidx hcl hsz1 hszP in
omit [Fintype ι] in
/-- **The total weight is the number of copies.** -/
theorem sum_placeWt :
    ∑ U ∈ placeFam P idx cl sz, placeWt P sz U = (Fintype.card κ : ℝ) := by
  classical
  rw [sum_placeFam hidx hcl hsz1]
  have hone : ∀ c : κ,
      ∑ A ∈ BoxCount.plc P (sz c), placeWt P sz (placeEdge idx cl c A) = 1 := by
    intro c
    have hpos : 0 < placeCard P sz c := placeCard_pos hszP c
    have hposR : (0 : ℝ) < (placeCard P sz c : ℝ) := by exact_mod_cast hpos
    simp only [placeWt_edge]
    rw [Finset.sum_const, nsmul_eq_mul]
    have : (#(BoxCount.plc P (sz c)) : ℝ) = (placeCard P sz c : ℝ) := rfl
    rw [this]
    field_simp
  rw [Finset.sum_congr rfl (fun c _ => hone c), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]

include hcl in
omit [Fintype ι] in
/-- Every edge is nonempty and has at most `1 + 3s₀²` vertices. -/
theorem placeFam_edge_size {s₀ : ℕ} (hs : ∀ c a, sz c a ≤ s₀) (U : Finset (PlaceVtx ι κ P))
    (hU : U ∈ placeFam P idx cl sz) : U.Nonempty ∧ #U ≤ 1 + 3 * s₀ ^ 2 := by
  obtain ⟨c, A, hA, rfl⟩ := mem_placeFam hU
  constructor
  · exact ⟨Sum.inr c, (mem_placeEdge_inr (A := A) (idx := idx) c).mpr rfl⟩
  · rw [placeEdge_card (hcl c)]
    have hbound : ∀ a : ZMod 3, #(A a) * #(A (a + 1)) ≤ s₀ ^ 2 := by
      intro a
      rw [BoxCount.mem_plc.mp hA a, BoxCount.mem_plc.mp hA (a + 1), sq]
      exact Nat.mul_le_mul (hs c a) (hs c (a + 1))
    have hsum : ∑ a : ZMod 3, #(A a) * #(A (a + 1)) ≤ 3 * s₀ ^ 2 := by
      calc ∑ a : ZMod 3, #(A a) * #(A (a + 1)) ≤ ∑ _a : ZMod 3, s₀ ^ 2 :=
            Finset.sum_le_sum fun a _ => hbound a
        _ = 3 * s₀ ^ 2 := by simp [ZMod.card, mul_comm]
    omega

end Structure

/-! ### The count of the placements of one copy through a prescribed slot -/

/-- Two ordered pairs of distinct residues mod `3` that agree neither directly nor after a swap
have a residue outside the first pair inside the second. -/
private theorem zmod3_third : ∀ p q p' q' : ZMod 3, p ≠ q → p' ≠ q' →
    ¬ (p = p' ∧ q = q') → ¬ (p = q' ∧ q = p') →
    ∃ t : ZMod 3, t ≠ p ∧ t ≠ q ∧ (t = p' ∨ t = q') := by
  change ∀ p q p' q' : Fin 3, p ≠ q → p' ≠ q' →
    ¬ (p = p' ∧ q = q') → ¬ (p = q' ∧ q = p') →
    ∃ t : Fin 3, t ≠ p ∧ t ≠ q ∧ (t = p' ∨ t = q')
  decide

section PerCopy

variable {c : κ}

omit [Fintype κ] [DecidableEq κ] in
theorem sum_inv_const (F : Finset (ZMod 3 → Finset (Fin P))) :
    ∑ _A ∈ F, ((placeCard P sz c : ℝ))⁻¹ = (#F : ℝ) * ((placeCard P sz c : ℝ))⁻¹ := by
  rw [Finset.sum_const, nsmul_eq_mul]

omit [Fintype ι] [Fintype κ] in
/-- **The placements of `c` occupying a prescribed slot**: either there are none, or the slot is
the cell pair `(i, j)` of two clusters `cl c p`, `cl c q` of `c`, and then they are at most a
`sz(c,p)·sz(c,q)/P²` fraction of all placements. -/
theorem slot_count_core (hidx : Function.Injective idx) (hcl : Function.Injective (cl c))
    (hszP : ∀ a, sz c a ≤ P) (hP : 0 < P) (S T : ι) (i j : Fin P)
    {F : Finset (ZMod 3 → Finset (Fin P))} (hFsub : F ⊆ BoxCount.plc P (sz c))
    (hF : ∀ A ∈ F, (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A) :
    F = ∅ ∨ ∃ p q : ZMod 3, p ≠ q ∧ cl c p = S ∧ cl c q = T ∧
      (#F : ℝ) * ((placeCard P sz c : ℝ))⁻¹ ≤ (sz c p : ℝ) * (sz c q : ℝ) / (P : ℝ) ^ 2 := by
  classical
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hNpos : 0 < placeCard P sz c := BoxCount.card_plc_pos hszP
  have hNR : (0 : ℝ) < (placeCard P sz c : ℝ) := by exact_mod_cast hNpos
  by_cases hex : ∃ p q : ZMod 3, p ≠ q ∧ cl c p = S ∧ cl c q = T ∧ idx S < idx T
  · obtain ⟨p, q, hpq, hp, hq, hlt⟩ := hex
    refine Or.inr ⟨p, q, hpq, hp, hq, ?_⟩
    set G := (BoxCount.plc P (sz c)).filter (fun A => i ∈ A p ∧ j ∈ A q) with hGdef
    have hFG : F ⊆ G := by
      intro A hA
      rw [hGdef, Finset.mem_filter]
      refine ⟨hFsub hA, ?_⟩
      obtain ⟨u, v, -, hu, hv, -, hiu, hjv⟩ := (mem_placeEdge_inl hidx hcl S T i j).mp (hF A hA)
      have e1 : u = p := hcl (hu.trans hp.symm)
      have e2 : v = q := hcl (hv.trans hq.symm)
      subst e1; subst e2
      exact ⟨hiu, hjv⟩
    have hcount := BoxCount.card_two (u := sz c) hszP hpq i j
    have hcard : (#F : ℝ) ≤ (#G : ℝ) := by exact_mod_cast Finset.card_le_card hFG
    have hcountR : (#G : ℝ) * ((P : ℝ) * (P : ℝ))
        = (sz c p : ℝ) * (sz c q : ℝ) * (placeCard P sz c : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hcount
    rw [inv_eq_one_div, mul_one_div, div_le_div_iff₀ hNR (by positivity), sq]
    linarith only [mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ (P : ℝ) * (P : ℝ)),
      hcountR]
  · refine Or.inl (Finset.eq_empty_of_forall_notMem fun A hA => ?_)
    obtain ⟨p, q, hpq, h1, h2, hlt, -, -⟩ := (mem_placeEdge_inl hidx hcl S T i j).mp (hF A hA)
    exact hex ⟨p, q, hpq, h1, h2, hlt⟩

omit [Fintype ι] [Fintype κ] in
/-- **The placements of `c` through a slot of `(S,T)` are a `demand/P²` fraction.** -/
theorem slot_count_le_demand (hidx : Function.Injective idx) (hcl : Function.Injective (cl c))
    (hszP : ∀ a, sz c a ≤ P) (hP : 0 < P) (S T : ι) (i j : Fin P)
    {F : Finset (ZMod 3 → Finset (Fin P))} (hFsub : F ⊆ BoxCount.plc P (sz c))
    (hF : ∀ A ∈ F, (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A) :
    ∑ _A ∈ F, ((placeCard P sz c : ℝ))⁻¹ ≤ boxDemandC cl sz c S T / (P : ℝ) ^ 2 := by
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  rw [sum_inv_const]
  rcases slot_count_core hidx hcl hszP hP S T i j hFsub hF with rfl | ⟨p, q, -, hp, hq, h⟩
  · simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    exact div_nonneg (boxDemandC_nonneg c S T) (by positivity)
  · refine le_trans h ?_
    gcongr
    exact sz_mul_le_boxDemandC hp hq

omit [Fintype ι] [Fintype κ] in
/-- The same count is at most `s₀²/P²`. -/
theorem slot_count_le_sz (hidx : Function.Injective idx) (hcl : Function.Injective (cl c))
    (hszP : ∀ a, sz c a ≤ P) (hP : 0 < P) {s₀ : ℕ} (hs : ∀ a, sz c a ≤ s₀) (S T : ι)
    (i j : Fin P) {F : Finset (ZMod 3 → Finset (Fin P))} (hFsub : F ⊆ BoxCount.plc P (sz c))
    (hF : ∀ A ∈ F, (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A) :
    ∑ _A ∈ F, ((placeCard P sz c : ℝ))⁻¹ ≤ (s₀ : ℝ) ^ 2 / (P : ℝ) ^ 2 := by
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  rw [sum_inv_const]
  rcases slot_count_core hidx hcl hszP hP S T i j hFsub hF with rfl | ⟨p, q, -, -, -, h⟩
  · simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity
  · refine le_trans h ?_
    have h1 : (sz c p : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hs p
    have h2 : (sz c q : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hs q
    have h3 : (0 : ℝ) ≤ (sz c p : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ (sz c q : ℝ) := Nat.cast_nonneg _
    gcongr
    nlinarith

omit [Fintype ι] [Fintype κ] in
/-- **Two slots pin a copy down in a third coordinate.**  This is the estimate that makes the
codegrees of the placement hypergraph small, and it is where the small-box restriction enters. -/
theorem two_slot_count_le (hidx : Function.Injective idx) (hcl : Function.Injective (cl c))
    (hszP : ∀ a, sz c a ≤ P) (hP : 2 ≤ P) {s₀ : ℕ} (hs : ∀ a, sz c a ≤ s₀) {S T S' T' : ι}
    {i j i' j' : Fin P} (hne : (S, T, i, j) ≠ (S', T', i', j'))
    {F : Finset (ZMod 3 → Finset (Fin P))} (hFsub : F ⊆ BoxCount.plc P (sz c))
    (hF1 : ∀ A ∈ F, (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A)
    (hF2 : ∀ A ∈ F, (Sum.inl (S', T', i', j') : PlaceVtx ι κ P) ∈ placeEdge idx cl c A) :
    ∑ _A ∈ F, ((placeCard P sz c : ℝ))⁻¹
      ≤ 18 * (s₀ : ℝ) / (P : ℝ) * (boxDemandC cl sz c S T / (P : ℝ) ^ 2) := by
  classical
  have hP0 : 0 < P := by omega
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP0
  have hNpos : 0 < placeCard P sz c := BoxCount.card_plc_pos hszP
  have hNR : (0 : ℝ) < (placeCard P sz c : ℝ) := by exact_mod_cast hNpos
  have hnn : 0 ≤ 18 * (s₀ : ℝ) / (P : ℝ) * (boxDemandC cl sz c S T / (P : ℝ) ^ 2) := by
    have := boxDemandC_nonneg (cl := cl) (sz := sz) c S T
    positivity
  rw [sum_inv_const]
  by_cases hex : ∃ p q : ZMod 3, p ≠ q ∧ cl c p = S ∧ cl c q = T ∧ idx S < idx T
  · obtain ⟨p, q, hpq, hp, hq, hlt⟩ := hex
    by_cases hex' : ∃ p' q' : ZMod 3, p' ≠ q' ∧ cl c p' = S' ∧ cl c q' = T' ∧ idx S' < idx T'
    · obtain ⟨p', q', hpq', hp', hq', hlt'⟩ := hex'
      have hmemF : ∀ A ∈ F, i ∈ A p ∧ j ∈ A q ∧ i' ∈ A p' ∧ j' ∈ A q' := by
        intro A hA
        obtain ⟨u, v, -, hu, hv, -, hiu, hjv⟩ :=
          (mem_placeEdge_inl hidx hcl S T i j).mp (hF1 A hA)
        obtain ⟨u', v', -, hu', hv', -, hiu', hjv'⟩ :=
          (mem_placeEdge_inl hidx hcl S' T' i' j').mp (hF2 A hA)
        have e1 : u = p := hcl (hu.trans hp.symm)
        have e2 : v = q := hcl (hv.trans hq.symm)
        have e3 : u' = p' := hcl (hu'.trans hp'.symm)
        have e4 : v' = q' := hcl (hv'.trans hq'.symm)
        subst e1; subst e2; subst e3; subst e4
        exact ⟨hiu, hjv, hiu', hjv'⟩
      have hPcube : P ^ 3 ≤ 2 * (P * (P - 1) * P) := by
        have hstep : P ≤ 2 * (P - 1) := by omega
        calc P ^ 3 = P * P * P := by ring
          _ ≤ (2 * (P - 1)) * P * P := by
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hstep)
          _ = 2 * (P * (P - 1) * P) := by ring
      have hkey : #F * P ^ 3 ≤ 2 * s₀ * sz c p * sz c q * placeCard P sz c := by
        by_cases hcase : p = p' ∧ q = q'
        · obtain ⟨hpp, hqq⟩ := hcase
          subst hpp; subst hqq
          have hST : S = S' := hp.symm.trans hp'
          have hTT : T = T' := hq.symm.trans hq'
          subst hST; subst hTT
          by_cases hii : i = i'
          · subst hii
            have hjj : j ≠ j' := by
              intro h
              exact hne (by rw [h])
            set G := (BoxCount.plc P (sz c)).filter
              (fun A => j ∈ A q ∧ j' ∈ A q ∧ i ∈ A p) with hGdef
            have hFG : F ⊆ G := by
              intro A hA
              obtain ⟨h1, h2, h3, h4⟩ := hmemF A hA
              rw [hGdef, Finset.mem_filter]
              exact ⟨hFsub hA, h2, h4, h1⟩
            have hcount := BoxCount.card_two_one (u := sz c) hszP (Ne.symm hpq) hjj i
            have hGle : #G * (P * (P - 1) * P) ≤ s₀ * sz c p * sz c q * placeCard P sz c := by
              rw [hcount]
              have h5 : sz c q - 1 ≤ s₀ := le_trans (Nat.sub_le _ _) (hs q)
              calc sz c q * (sz c q - 1) * sz c p * placeCard P sz c
                  ≤ sz c q * s₀ * sz c p * placeCard P sz c :=
                    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h5))
                _ = s₀ * sz c p * sz c q * placeCard P sz c := by ring
            calc #F * P ^ 3 ≤ #G * (2 * (P * (P - 1) * P)) :=
                  Nat.mul_le_mul (Finset.card_le_card hFG) hPcube
              _ = 2 * (#G * (P * (P - 1) * P)) := by ring
              _ ≤ 2 * (s₀ * sz c p * sz c q * placeCard P sz c) := Nat.mul_le_mul_left _ hGle
              _ = 2 * s₀ * sz c p * sz c q * placeCard P sz c := by ring
          · set G := (BoxCount.plc P (sz c)).filter
              (fun A => i ∈ A p ∧ i' ∈ A p ∧ j ∈ A q) with hGdef
            have hFG : F ⊆ G := by
              intro A hA
              obtain ⟨h1, h2, h3, h4⟩ := hmemF A hA
              rw [hGdef, Finset.mem_filter]
              exact ⟨hFsub hA, h1, h3, h2⟩
            have hcount := BoxCount.card_two_one (u := sz c) hszP hpq hii j
            have hGle : #G * (P * (P - 1) * P) ≤ s₀ * sz c p * sz c q * placeCard P sz c := by
              rw [hcount]
              have h5 : sz c p - 1 ≤ s₀ := le_trans (Nat.sub_le _ _) (hs p)
              calc sz c p * (sz c p - 1) * sz c q * placeCard P sz c
                  ≤ sz c p * s₀ * sz c q * placeCard P sz c :=
                    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h5))
                _ = s₀ * sz c p * sz c q * placeCard P sz c := by ring
            calc #F * P ^ 3 ≤ #G * (2 * (P * (P - 1) * P)) :=
                  Nat.mul_le_mul (Finset.card_le_card hFG) hPcube
              _ = 2 * (#G * (P * (P - 1) * P)) := by ring
              _ ≤ 2 * (s₀ * sz c p * sz c q * placeCard P sz c) := Nat.mul_le_mul_left _ hGle
              _ = 2 * s₀ * sz c p * sz c q * placeCard P sz c := by ring
        · have hswap : ¬ (p = q' ∧ q = p') := by
            rintro ⟨h1, h2⟩
            have e1 : S = T' := by rw [← hp, h1, hq']
            have e2 : T = S' := by rw [← hq, h2, hp']
            rw [e1, e2] at hlt
            omega
          obtain ⟨t, htp, htq, ht⟩ := zmod3_third p q p' q' hpq hpq' hcase hswap
          have hpt : p ≠ t := Ne.symm htp
          have hqt : q ≠ t := Ne.symm htq
          set z : Fin P := if t = p' then i' else j' with hzdef
          have hzmem : ∀ A ∈ F, z ∈ A t := by
            intro A hA
            obtain ⟨-, -, h3, h4⟩ := hmemF A hA
            by_cases hcase2 : t = p'
            · rw [hzdef, ite_eq_left hcase2, hcase2]
              exact h3
            · rw [hzdef, ite_eq_right hcase2]
              rcases ht with h | h
              · exact absurd h hcase2
              · rw [h]; exact h4
          set G := (BoxCount.plc P (sz c)).filter
            (fun A => i ∈ A p ∧ j ∈ A q ∧ z ∈ A t) with hGdef
          have hFG : F ⊆ G := by
            intro A hA
            obtain ⟨h1, h2, -, -⟩ := hmemF A hA
            rw [hGdef, Finset.mem_filter]
            exact ⟨hFsub hA, h1, h2, hzmem A hA⟩
          have hcount := BoxCount.card_three (u := sz c) hszP hpq hpt hqt i j z
          have hGle : #G * (P * P * P) ≤ s₀ * sz c p * sz c q * placeCard P sz c := by
            rw [hcount]
            calc sz c p * sz c q * sz c t * placeCard P sz c
                ≤ sz c p * sz c q * s₀ * placeCard P sz c :=
                  Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hs t))
              _ = s₀ * sz c p * sz c q * placeCard P sz c := by ring
          have hcube : P ^ 3 = P * P * P := by ring
          calc #F * P ^ 3 ≤ #G * (P * P * P) := by
                rw [hcube]
                exact Nat.mul_le_mul_right _ (Finset.card_le_card hFG)
            _ ≤ s₀ * sz c p * sz c q * placeCard P sz c := hGle
            _ ≤ 2 * (s₀ * sz c p * sz c q * placeCard P sz c) :=
                Nat.le_mul_of_pos_left _ (by norm_num)
            _ = 2 * s₀ * sz c p * sz c q * placeCard P sz c := by ring
      have hkeyR : (#F : ℝ) * (P : ℝ) ^ 3
          ≤ 2 * (s₀ : ℝ) * (sz c p : ℝ) * (sz c q : ℝ) * (placeCard P sz c : ℝ) := by
        exact_mod_cast hkey
      have hdem : (sz c p : ℝ) * (sz c q : ℝ) ≤ boxDemandC cl sz c S T :=
        sz_mul_le_boxDemandC hp hq
      have hs0 : (0 : ℝ) ≤ (s₀ : ℝ) := Nat.cast_nonneg _
      have hfinal : (#F : ℝ) * ((placeCard P sz c : ℝ))⁻¹
          ≤ 2 * (s₀ : ℝ) * ((sz c p : ℝ) * (sz c q : ℝ)) / (P : ℝ) ^ 3 := by
        rw [le_div_iff₀ (by positivity)]
        calc (#F : ℝ) * ((placeCard P sz c : ℝ))⁻¹ * (P : ℝ) ^ 3
            = ((#F : ℝ) * (P : ℝ) ^ 3) * ((placeCard P sz c : ℝ))⁻¹ := by ring
          _ ≤ (2 * (s₀ : ℝ) * (sz c p : ℝ) * (sz c q : ℝ) * (placeCard P sz c : ℝ))
              * ((placeCard P sz c : ℝ))⁻¹ := by
              gcongr
          _ = 2 * (s₀ : ℝ) * ((sz c p : ℝ) * (sz c q : ℝ)) := by
              field_simp
      refine le_trans hfinal ?_
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have hdnn : (0 : ℝ) ≤ boxDemandC cl sz c S T := boxDemandC_nonneg c S T
      have hmain : 2 * (s₀ : ℝ) * ((sz c p : ℝ) * (sz c q : ℝ))
          ≤ 18 * (s₀ : ℝ) * boxDemandC cl sz c S T := by
        linarith only [mul_nonneg hs0 (sub_nonneg.2 hdem), mul_nonneg hs0 hdnn]
      have hP3 : (0 : ℝ) ≤ (P : ℝ) ^ 3 := by positivity
      linarith only [mul_le_mul_of_nonneg_right hmain hP3, hP3]
    · have hempty : F = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun A hA => ?_
        obtain ⟨u, v, huv, hu, hv, hlt2, -, -⟩ :=
          (mem_placeEdge_inl hidx hcl S' T' i' j').mp (hF2 A hA)
        exact hex' ⟨u, v, huv, hu, hv, hlt2⟩
      rw [hempty]
      simpa using hnn
  · have hempty : F = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun A hA => ?_
      obtain ⟨u, v, huv, hu, hv, hlt2, -, -⟩ := (mem_placeEdge_inl hidx hcl S T i j).mp (hF1 A hA)
      exact hex ⟨u, v, huv, hu, hv, hlt2⟩
    rw [hempty]
    simpa using hnn

end PerCopy

/-! ### The loads and the codegrees -/

section Estimates

variable (hidx : Function.Injective idx) (hcl : ∀ c, Function.Injective (cl c))
  (hsz1 : ∀ c a, 1 ≤ sz c a) (hszP : ∀ c a, sz c a ≤ P)

include hidx hcl hsz1 hszP in
omit [Fintype ι] in
/-- The load of a token is exactly `1`. -/
theorem wLoad_inr (c : κ) :
    Slack.wLoad (placeFam P idx cl sz) (placeWt P sz) (Sum.inr c) = 1 := by
  classical
  rw [Slack.wLoad, sum_placeFam_filter hidx hcl hsz1]
  have hterm : ∀ c' : κ,
      ∑ A ∈ (BoxCount.plc P (sz c')).filter
          (fun A => (Sum.inr c : PlaceVtx ι κ P) ∈ placeEdge idx cl c' A),
        placeWt P sz (placeEdge idx cl c' A) = if c' = c then 1 else 0 := by
    intro c'
    by_cases hcc : c' = c
    · subst hcc
      have hfil : (BoxCount.plc P (sz c')).filter
          (fun A => (Sum.inr c' : PlaceVtx ι κ P) ∈ placeEdge idx cl c' A)
          = BoxCount.plc P (sz c') := by
        refine Finset.filter_true_of_mem fun A _ => ?_
        exact (mem_placeEdge_inr (A := A) (idx := idx) c').mpr rfl
      rw [hfil, ite_eq_left rfl]
      have hpos : 0 < placeCard P sz c' := placeCard_pos hszP c'
      have hposR : (0 : ℝ) < (placeCard P sz c' : ℝ) := by exact_mod_cast hpos
      simp only [placeWt_edge]
      rw [Finset.sum_const, nsmul_eq_mul]
      have : (#(BoxCount.plc P (sz c')) : ℝ) = (placeCard P sz c' : ℝ) := rfl
      rw [this]
      field_simp
    · rw [ite_eq_right hcc]
      refine Finset.sum_eq_zero fun A hA => ?_
      exfalso
      rw [Finset.mem_filter, mem_placeEdge_inr] at hA
      exact hcc hA.2.symm
  rw [Finset.sum_congr rfl (fun c' _ => hterm c'),
    Finset.sum_ite_eq' Finset.univ c (fun _ => (1 : ℝ))]
  simp

include hidx hcl hsz1 in
omit [Fintype ι] in
/-- Only the slots oriented by `idx` are occupied. -/
theorem wLoad_inl_of_not_lt {S T : ι} (h : ¬ idx S < idx T) (i j : Fin P) :
    Slack.wLoad (placeFam P idx cl sz) (placeWt P sz) (Sum.inl (S, T, i, j)) = 0 := by
  classical
  rw [Slack.wLoad, sum_placeFam_filter hidx hcl hsz1]
  refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun A hA => ?_
  exfalso
  rw [Finset.mem_filter] at hA
  obtain ⟨-, hmem⟩ := hA
  obtain ⟨-, -, -, -, -, hlt, -, -⟩ := (mem_placeEdge_inl hidx (hcl c) S T i j).mp hmem
  exact h hlt

include hidx hcl hsz1 hszP in
omit [Fintype ι] in
/-- **The load of a slot is at most the normalised demand of its cluster pair.** -/
theorem wLoad_inl_le (hP : 0 < P) (S T : ι) (i j : Fin P) :
    Slack.wLoad (placeFam P idx cl sz) (placeWt P sz) (Sum.inl (S, T, i, j))
      ≤ boxDemand cl sz S T / (P : ℝ) ^ 2 := by
  classical
  rw [Slack.wLoad, sum_placeFam_filter hidx hcl hsz1, boxDemand_eq_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun c _ => ?_
  have hEq : ∑ A ∈ (BoxCount.plc P (sz c)).filter
      (fun A => (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A),
      placeWt P sz (placeEdge idx cl c A)
      = ∑ A ∈ (BoxCount.plc P (sz c)).filter
      (fun A => (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A),
      ((placeCard P sz c : ℝ))⁻¹ :=
    Finset.sum_congr rfl fun A _ => placeWt_edge c A
  rw [hEq]
  exact slot_count_le_demand hidx (hcl c) (fun a => hszP c a) hP S T i j
    (Finset.filter_subset _ _) (fun A hA => (Finset.mem_filter.mp hA).2)

omit [Fintype ι] in
/-- Two tokens are never together in an edge. -/
theorem codeg_inr_inr {c c' : κ} (h : c ≠ c') :
    ∑ U ∈ ((placeFam P idx cl sz).filter (fun U => (Sum.inr c : PlaceVtx ι κ P) ∈ U)).filter
        (fun U => (Sum.inr c' : PlaceVtx ι κ P) ∈ U),
      placeWt P sz U = 0 := by
  refine Finset.sum_eq_zero fun U hU => ?_
  exfalso
  rw [Finset.mem_filter, Finset.mem_filter] at hU
  obtain ⟨⟨hUK, hc⟩, hc'⟩ := hU
  obtain ⟨d, A, -, rfl⟩ := mem_placeFam hUK
  rw [mem_placeEdge_inr] at hc hc'
  exact h (hc.trans hc'.symm)

include hidx hcl hsz1 hszP in
omit [Fintype ι] in
/-- **The codegree of a slot and a token** is at most `9 s₀²/P²`. -/
theorem codeg_inl_inr_le (hP : 0 < P) {s₀ : ℕ} (hs : ∀ c a, sz c a ≤ s₀) (c : κ) (S T : ι)
    (i j : Fin P) :
    ∑ U ∈ ((placeFam P idx cl sz).filter
          (fun U => (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ U)).filter
        (fun U => (Sum.inr c : PlaceVtx ι κ P) ∈ U),
      placeWt P sz U ≤ 9 * (s₀ : ℝ) ^ 2 / (P : ℝ) ^ 2 := by
  classical
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  rw [Finset.filter_filter, sum_placeFam_filter hidx hcl hsz1]
  refine le_trans (Finset.sum_le_sum
    (g := fun c' : κ => if c' = c then (s₀ : ℝ) ^ 2 / (P : ℝ) ^ 2 else 0)
    (fun c' _ => ?_)) ?_
  · change _ ≤ (if c' = c then (s₀ : ℝ) ^ 2 / (P : ℝ) ^ 2 else 0)
    by_cases hcc : c' = c
    · subst hcc
      rw [ite_eq_left rfl, Finset.sum_congr rfl (fun A _ => placeWt_edge c' A)]
      refine slot_count_le_sz hidx (hcl c') (fun a => hszP c' a) hP (fun a => hs c' a) S T i j
        ?_ ?_
      · intro A hA
        simp only [Finset.mem_filter] at hA
        exact hA.1
      · intro A hA
        simp only [Finset.mem_filter] at hA
        exact hA.2.1
    · rw [ite_eq_right hcc]
      refine le_of_eq (Finset.sum_eq_zero fun A hA => ?_)
      exfalso
      simp only [Finset.mem_filter] at hA
      obtain ⟨-, -, h2⟩ := hA
      rw [mem_placeEdge_inr] at h2
      exact hcc h2.symm
  · rw [Finset.sum_ite_eq' Finset.univ c (fun _ => (s₀ : ℝ) ^ 2 / (P : ℝ) ^ 2)]
    rw [ite_eq_left (Finset.mem_univ c)]
    have h9 : (0 : ℝ) ≤ (s₀ : ℝ) ^ 2 := sq_nonneg _
    rw [div_le_div_iff_of_pos_right (by positivity)]
    linarith

include hidx hcl hsz1 hszP in
omit [Fintype ι] in
/-- **The codegree of two slots** is `O(s₀/P)` times the normalised demand: two placements sharing
two slots are pinned down in one further coordinate.  This is where the small-box restriction is
used. -/
theorem codeg_inl_inl_le (hP : 2 ≤ P) {s₀ : ℕ} (hs : ∀ c a, sz c a ≤ s₀) {S T S' T' : ι}
    {i j i' j' : Fin P} (hne : (S, T, i, j) ≠ (S', T', i', j')) :
    ∑ U ∈ ((placeFam P idx cl sz).filter
          (fun U => (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ U)).filter
        (fun U => (Sum.inl (S', T', i', j') : PlaceVtx ι κ P) ∈ U),
      placeWt P sz U
      ≤ 18 * (s₀ : ℝ) / (P : ℝ) * (boxDemand cl sz S T / (P : ℝ) ^ 2) := by
  classical
  have hP0 : 0 < P := by omega
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP0
  rw [Finset.filter_filter, sum_placeFam_filter hidx hcl hsz1, boxDemand_eq_sum]
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [Finset.sum_congr rfl (fun A _ => placeWt_edge c A)]
  refine two_slot_count_le hidx (hcl c) (fun a => hszP c a) hP (fun a => hs c a) hne ?_ ?_ ?_
  · intro A hA
    simp only [Finset.mem_filter] at hA
    exact hA.1
  · intro A hA
    simp only [Finset.mem_filter] at hA
    exact hA.2.1
  · intro A hA
    simp only [Finset.mem_filter] at hA
    exact hA.2.2

include hidx hcl hsz1 hszP in
omit [Fintype ι] in
/-- **All weighted codegrees are `O(s₀/P)`.** -/
theorem codeg_le (hP : 2 ≤ P) {s₀ : ℕ} (hs : ∀ c a, sz c a ≤ s₀) (hsP : s₀ ≤ P)
    (hdem : ∀ S T : ι, S ≠ T → boxDemand cl sz S T ≤ (P : ℝ) ^ 2)
    (x z : PlaceVtx ι κ P) (hxz : x ≠ z) :
    ∑ U ∈ ((placeFam P idx cl sz).filter (fun U => x ∈ U)).filter (fun U => z ∈ U),
      placeWt P sz U ≤ 18 * (s₀ : ℝ) / (P : ℝ) := by
  classical
  have hP0 : 0 < P := by omega
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP0
  have hsPR : (s₀ : ℝ) ≤ (P : ℝ) := by exact_mod_cast hsP
  have hs0R : (0 : ℝ) ≤ (s₀ : ℝ) := Nat.cast_nonneg _
  have hslotzero : ∀ (S T : ι) (i j : Fin P), ¬ idx S < idx T →
      ∀ (p : Finset (PlaceVtx ι κ P) → Prop) [DecidablePred p],
      ∑ U ∈ ((placeFam P idx cl sz).filter
          (fun U => (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ U)).filter p,
        placeWt P sz U = 0 := by
    intro S T i j hlt p _
    refine Finset.sum_eq_zero fun U hU => ?_
    exfalso
    rw [Finset.mem_filter, Finset.mem_filter] at hU
    obtain ⟨⟨hUK, hmem⟩, -⟩ := hU
    obtain ⟨c, A, -, rfl⟩ := mem_placeFam hUK
    obtain ⟨-, -, -, -, -, hlt2, -, -⟩ := (mem_placeEdge_inl hidx (hcl c) S T i j).mp hmem
    exact hlt hlt2
  match x, z with
  | Sum.inr c, Sum.inr c' =>
      have hcc : c ≠ c' := fun h => hxz (by rw [h])
      rw [codeg_inr_inr hcc]
      positivity
  | Sum.inl (S, T, i, j), Sum.inr c =>
      refine le_trans (codeg_inl_inr_le hidx hcl hsz1 hszP hP0 hs c S T i j) ?_
      rw [div_le_div_iff₀ (by positivity) hPR]
      nlinarith only [hs0R, hsPR, hPR, mul_nonneg hs0R (le_of_lt hPR),
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsPR hs0R) (le_of_lt hPR)]
  | Sum.inr c, Sum.inl (S, T, i, j) =>
      have hset : ((placeFam P idx cl sz).filter
            (fun U => (Sum.inr c : PlaceVtx ι κ P) ∈ U)).filter
              (fun U => (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ U)
          = ((placeFam P idx cl sz).filter
            (fun U => (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ U)).filter
              (fun U => (Sum.inr c : PlaceVtx ι κ P) ∈ U) := by
        ext U
        simp only [Finset.mem_filter]
        tauto
      rw [hset]
      refine le_trans (codeg_inl_inr_le hidx hcl hsz1 hszP hP0 hs c S T i j) ?_
      rw [div_le_div_iff₀ (by positivity) hPR]
      nlinarith only [hs0R, hsPR, hPR, mul_nonneg hs0R (le_of_lt hPR),
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsPR hs0R) (le_of_lt hPR)]
  | Sum.inl (S, T, i, j), Sum.inl (S', T', i', j') =>
      have hne : (S, T, i, j) ≠ (S', T', i', j') := by
        intro h
        exact hxz (by rw [h])
      by_cases hlt : idx S < idx T
      · have hST : S ≠ T := by
          intro h
          rw [h] at hlt
          exact lt_irrefl _ hlt
        refine le_trans (codeg_inl_inl_le hidx hcl hsz1 hszP hP hs hne) ?_
        have hdd : boxDemand cl sz S T / (P : ℝ) ^ 2 ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact hdem S T hST
        have hfac : (0 : ℝ) ≤ 18 * (s₀ : ℝ) / (P : ℝ) := by positivity
        nlinarith only [hdd, hfac]
      · rw [hslotzero S T i j hlt]
        positivity

end Estimates

end BoxPlace

end Nibble.AX1
