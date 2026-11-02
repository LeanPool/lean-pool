/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import LeanPool.Erdos111.Closure
public import LeanPool.Erdos111.Successor.Forcing

/-!
# The key inequality of the successor step

Let `N` be closed over `M`, let `ν` satisfy `J` over `M`, and force the signs of the set
`X` of new vertices with infinite trace. For finitely many patterns `P i` over `N` and
nonnegative weights `ρ i`, the expected weighted cost, after choosing the signs of the
remaining roots `W` (new vertices with finite trace) jointly and optimally, is at most
`∑ ρ i C |S i|`.

*Proof.* Fix `k` and take `⌈k ρ i⌉` copies of each `S i` over its roots inside
`N \ M`, pairwise disjoint and avoiding all roots, by `ClosedOver`. Together with stars
from each root `y ∈ X` to `a y 0, …, a y (L - 1)` they form one pattern over `M`, to
which `J` applies. Almost surely, once `L` exceeds the number of disagreements along
`a y` plus the total copy weight, every cheap extension gives each `y` its forced sign,
so the pattern costs at least `k` times the left-hand integrand. Fatou's lemma in `L`,
division by `k`, and `k → ∞` give the bound.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Erdos111

variable {V : Type*}

/-! ### Monochromatic counts -/

open Classical in
/-- The monochromatic count is monotone in the edge set. -/
theorem monoCount_le_of_subset {E F : Finset (Sym2 V)} (h : E ⊆ F) (τ : V → Bool) :
    monoCount E τ ≤ monoCount F τ :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

open Classical in
/-- `Sym2.map φ` is injective on the edges inside a set on which `φ` is injective. -/
theorem injOn_sym2Map_of_injOn {φ : V → V} {A : Set V} (hφ : Set.InjOn φ A)
    {E : Finset (Sym2 V)} (hE : ∀ e ∈ E, ∀ v ∈ e, v ∈ A) : Set.InjOn (Sym2.map φ) E := by
  have key : ∀ e e' : Sym2 V, (∀ v ∈ e, v ∈ A) → (∀ v ∈ e', v ∈ A) →
      Sym2.map φ e = Sym2.map φ e' → e = e' := by
    intro e e'
    induction e using Sym2.ind with
    | _ a b =>
      induction e' using Sym2.ind with
      | _ c d =>
        intro h h' he
        have ha := h a (Sym2.mem_mk_left a b)
        have hb := h b (Sym2.mem_mk_right a b)
        have hc := h' c (Sym2.mem_mk_left c d)
        have hd := h' d (Sym2.mem_mk_right c d)
        rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at he
        rw [Sym2.eq_iff]
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨hφ ha hc h1, hφ hb hd h2⟩
        · exact Or.inr ⟨hφ ha hd h1, hφ hb hc h2⟩
  intro e he e' he' h
  exact key e e' (hE e he) (hE e' he') h

open Classical in
/-- Transport of the monochromatic count along a map injective on the edges. -/
theorem monoCount_image_sym2Map {E : Finset (Sym2 V)} {φ : V → V}
    (hφ : Set.InjOn (Sym2.map φ) E) (τ : V → Bool) :
    monoCount (E.image (Sym2.map φ)) τ = monoCount E (τ ∘ φ) := by
  unfold monoCount
  rw [Finset.filter_image,
    Finset.card_image_of_injOn (hφ.mono fun x hx => by
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, SetLike.mem_coe] at hx ⊢
      exact hx.1)]
  congr 1
  refine Finset.filter_congr fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b => simp [mono]

/-! ### Copies of patterns -/

open Classical in
/-- `φ` copies the pattern `P` into `N`: it fixes every vertex off `P.S`, maps `P.S`
injectively into `N` away from `M` and `D`, and maps the edges of `P` to edges of `G`. -/
structure IsCopy (G : SimpleGraph V) (M N : Set V) (D : Finset V) (P : Pattern V)
    (φ : V → V) : Prop where
  /-- Every vertex off the new vertices is fixed. -/
  eq_self : ∀ v ∉ P.S, φ v = v
  /-- The new vertices are copied injectively. -/
  injOn : Set.InjOn φ P.S
  /-- The copied new vertices lie in `N`, outside `M` and `D`. -/
  mem : ∀ v ∈ P.S, φ v ∈ N ∧ φ v ∉ M ∧ φ v ∉ D
  /-- The copied edges are edges of `G`. -/
  edges : ∀ e ∈ P.E, Sym2.map φ e ∈ G.edgeSet

open Classical in
/-- A pattern over `N` has a copy in `N` avoiding `M` and a finite `D ⊆ N`. -/
theorem exists_copy {G : SimpleGraph V} {M N : Set V} (hMN : ClosedOver G M N)
    {P : Pattern V} (hP : P.IsOver G N) {D : Finset V} (hD : ↑D ⊆ N) :
    ∃ φ, IsCopy G M N D P φ := by
  let e := P.S.equivFin
  let f : Fin P.S.card → V := fun j => (e.symm j : V)
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  obtain ⟨g, hg, hgN, hgd⟩ := hMN.2 P.R D _ f hP.roots_subset hD hf fun j =>
    have h := hP.new_not_mem _ (e.symm j).2
    ⟨fun h' => h (hMN.1 h'), fun h' => h (hD h'), fun h' => h (hP.roots_subset h')⟩
  have key : ∀ v (hv : v ∈ P.S), f (e ⟨v, hv⟩) = v := fun v hv => by simp [f]
  refine ⟨fun v => if h : v ∈ P.S then g (e ⟨v, h⟩) else v, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro v hv
    simp [hv]
  · intro v hv w hw h
    simp only [Finset.mem_coe] at hv hw
    simp only [hv, hw, ↓reduceDIte] at h
    simpa using e.injective (hg h)
  · intro v hv
    simp only [hv, ↓reduceDIte]
    exact ⟨(hgN _).1, (hgN _).2.1, (hgN _).2.2.1⟩
  · intro x hx
    have hadj := hP.edges_subset hx
    have hin := hP.edges_inside x hx
    have hmeet := hP.edges_meet x hx
    clear hx
    induction x using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at hadj
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
      by_cases ha : a ∈ P.S <;> by_cases hb : b ∈ P.S
      · simp only [ha, hb, ↓reduceDIte]
        rw [← key a ha, ← key b hb] at hadj
        exact (hgd.1 _ _).1 hadj
      · simp only [ha, hb, ↓reduceDIte]
        have hbR := (hin b (Sym2.mem_mk_right a b)).resolve_right hb
        rw [← key a ha] at hadj
        exact (hgd.2 _ b hbR).1 hadj
      · simp only [ha, hb, ↓reduceDIte]
        have haR := (hin a (Sym2.mem_mk_left a b)).resolve_right ha
        rw [← key b hb] at hadj
        exact ((hgd.2 _ a haR).1 hadj.symm).symm
      · exfalso
        obtain ⟨v, hv, hvS⟩ := hmeet
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact ha hvS
        · exact hb hvS

open Classical in
/-- Finitely many patterns over `N` have copies in `N` avoiding `M` and a finite `D ⊆ N`,
with pairwise disjoint images of their new vertices. -/
theorem exists_copies {G : SimpleGraph V} {M N : Set V} (hMN : ClosedOver G M N)
    {ι : Type*} [Finite ι] (Q : ι → Pattern V) (hQ : ∀ j, (Q j).IsOver G N) {D : Finset V}
    (hD : ↑D ⊆ N) :
    ∃ φ : ι → V → V, (∀ j, IsCopy G M N D (Q j) (φ j)) ∧
      ∀ j j', j ≠ j' → ∀ v ∈ (Q j).S, ∀ v' ∈ (Q j').S, φ j v ≠ φ j' v' := by
  have := Fintype.ofFinite ι
  suffices h : ∀ T : Finset ι, ∃ φ : ι → V → V,
      (∀ j ∈ T, IsCopy G M N D (Q j) (φ j)) ∧
      ∀ j ∈ T, ∀ j' ∈ T, j ≠ j' →
        ∀ v ∈ (Q j).S, ∀ v' ∈ (Q j').S, φ j v ≠ φ j' v' by
    obtain ⟨φ, h1, h2⟩ := h Finset.univ
    exact ⟨φ, fun j => h1 j (Finset.mem_univ _),
      fun j j' hjj' => h2 j (Finset.mem_univ _) j' (Finset.mem_univ _) hjj'⟩
  intro T
  induction T using Finset.induction_on with
  | empty => exact ⟨fun _ => id, by simp, by simp⟩
  | insert a T ha ih =>
    obtain ⟨φ, h1, h2⟩ := ih
    let D' := D ∪ T.biUnion fun j => (Q j).S.image (φ j)
    have hD' : ↑D' ⊆ N := by
      intro x hx
      simp only [D', Finset.coe_union, Finset.coe_biUnion, Finset.coe_image, Set.mem_union,
        Set.mem_iUnion, Set.mem_image, Finset.mem_coe] at hx
      rcases hx with hx | ⟨j, hj, v, hv, rfl⟩
      · exact hD hx
      · exact ((h1 j hj).mem v hv).1
    obtain ⟨ψ, hψ⟩ := exists_copy hMN (hQ a) hD'
    have hψD : IsCopy G M N D (Q a) ψ :=
      ⟨hψ.eq_self, hψ.injOn, fun v hv =>
        ⟨(hψ.mem v hv).1, (hψ.mem v hv).2.1,
          fun h => (hψ.mem v hv).2.2 (Finset.mem_union_left _ h)⟩, hψ.edges⟩
    have hψT : ∀ j ∈ T, ∀ v ∈ (Q a).S, ∀ v' ∈ (Q j).S, ψ v ≠ φ j v' := by
      intro j hj v hv v' hv' h
      apply (hψ.mem v hv).2.2
      rw [h]
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨j, hj, Finset.mem_image_of_mem _ hv'⟩)
    have hupd : ∀ j ∈ T, Function.update φ a ψ j = φ j := fun j hj =>
      Function.update_of_ne (by rintro rfl; exact ha hj) _ _
    refine ⟨Function.update φ a ψ, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · simpa using hψD
      · rw [hupd j hj]
        exact h1 j hj
    · intro j hj j' hj' hjj'
      rcases Finset.mem_insert.1 hj with rfl | hjT <;>
        rcases Finset.mem_insert.1 hj' with rfl | hjT'
      · exact absurd rfl hjj'
      · simpa [hupd j' hjT'] using hψT j' hjT'
      · intro v hv v' hv'
        simpa [hupd j hjT] using (hψT j hjT v' hv' v hv).symm
      · simpa [hupd j hjT, hupd j' hjT'] using h2 j hjT j' hjT' hjj'

open Classical in
/-- A copy fixes the roots and is injective on the roots and new vertices together. -/
theorem IsCopy.injOn_union {G : SimpleGraph V} {M N : Set V} {D : Finset V} {P : Pattern V}
    {φ : V → V} (h : IsCopy G M N D P φ) (hRD : P.R ⊆ D) (hRS : ∀ v ∈ P.R, v ∉ P.S) :
    Set.InjOn φ ↑(P.R ∪ P.S) := by
  intro v hv w hw hvw
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hv hw
  rcases hv with hv | hv <;> rcases hw with hw | hw
  · rwa [h.eq_self v (hRS v hv), h.eq_self w (hRS w hw)] at hvw
  · rw [h.eq_self v (hRS v hv)] at hvw
    exact absurd (hvw ▸ hRD hv) (h.mem w hw).2.2
  · rw [h.eq_self w (hRS w hw)] at hvw
    exact absurd (hvw ▸ hRD hw) (h.mem v hv).2.2
  · exact h.injOn hv hw hvw

open Classical in
/-- A copy of `P` costs at least the extension cost of `P` under any signs agreeing on the
roots. -/
theorem IsCopy.extCost_le_monoCount {G : SimpleGraph V} {M N : Set V} {D : Finset V}
    {P : Pattern V} {φ : V → V} (h : IsCopy G M N D P φ) (hRD : P.R ⊆ D)
    (hRS : ∀ v ∈ P.R, v ∉ P.S) (hE : ∀ e ∈ P.E, ∀ v ∈ e, v ∈ P.R ∨ v ∈ P.S)
    {τ τ₀ : V → Bool} (hτ : ∀ v ∈ P.R, τ v = τ₀ v) :
    extCost P.S P.E τ₀ ≤ monoCount (P.E.image (Sym2.map φ)) τ := by
  rw [monoCount_image_sym2Map (injOn_sym2Map_of_injOn (h.injOn_union hRD hRS)
    fun e he v hv => by simpa using hE e he v hv)]
  rw [monoCount_congr (τ' := P.S.piecewise (τ ∘ φ) τ₀)]
  · exact Erdos111.extCost_le_monoCount _ _ _ _
  · intro e he v hv
    rcases hE e he v hv with hR | hS
    · rw [Finset.piecewise_eq_of_notMem _ _ _ (hRS v hR), Function.comp_apply,
        h.eq_self v (hRS v hR), hτ v hR]
    · rw [Finset.piecewise_eq_of_mem _ _ _ hS]

open Classical in
/-- Copies with disjoint new vertices avoiding all roots have disjoint edge sets. -/
theorem IsCopy.disjoint_edges {G : SimpleGraph V} {M N : Set V} {D : Finset V}
    {P Q : Pattern V} {φ ψ : V → V} (hφ : IsCopy G M N D P φ) (hψ : IsCopy G M N D Q ψ)
    (hP : P.IsOver G N) (hQ : Q.IsOver G N) (hQD : Q.R ⊆ D)
    (h : ∀ v ∈ P.S, ∀ v' ∈ Q.S, φ v ≠ ψ v') :
    Disjoint (P.E.image (Sym2.map φ)) (Q.E.image (Sym2.map ψ)) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.1 he
  obtain ⟨e₁, he₁, hee⟩ := Finset.mem_image.1 he'
  obtain ⟨v, hv, hvS⟩ := hP.edges_meet e₀ he₀
  have hmem : φ v ∈ Sym2.map ψ e₁ := hee ▸ Sym2.mem_map.2 ⟨v, hv, rfl⟩
  obtain ⟨w, hw, hwv⟩ := Sym2.mem_map.1 hmem
  rcases hQ.edges_inside e₁ he₁ w hw with hwR | hwS
  · have hwS : w ∉ Q.S := fun hwS => hQ.new_not_mem w hwS (hQ.roots_subset hwR)
    rw [hψ.eq_self w hwS] at hwv
    exact (hφ.mem v hvS).2.2 (hwv ▸ hQD hwR)
  · exact h v hvS w hwS hwv.symm

open Classical in
/-- The monochromatic count over a disjoint union of edge sets is the sum of the counts. -/
theorem monoCount_biUnion_of_pairwiseDisjoint {ι : Type*} {s : Finset ι}
    {t : ι → Finset (Sym2 V)} (h : (s : Set ι).PairwiseDisjoint t) (τ : V → Bool) :
    monoCount (s.biUnion t) τ = ∑ j ∈ s, monoCount (t j) τ := by
  unfold monoCount
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  exact fun j hj j' hj' hne =>
    (h hj hj' hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

open Classical in
/-- A sum over the copies is a sum over the patterns weighted by the numbers of copies. -/
theorem sum_sigma_fin {r : ℕ} (m : Fin r → ℕ) (x : Fin r → ℝ≥0∞) :
    ∑ j : (Σ i, Fin (m i)), x j.1 = ∑ i, (m i : ℝ≥0∞) * x i := by
  rw [Fintype.sum_sigma]
  simp

open Classical in
/-- The natural-number version of `sum_sigma_fin`. -/
theorem sum_sigma_fin_nat {r : ℕ} (m : Fin r → ℕ) (x : Fin r → ℕ) :
    ∑ j : (Σ i, Fin (m i)), x j.1 = ∑ i, m i * x i := by
  rw [Fintype.sum_sigma]
  simp

open Classical in
/-- An inequality `k I ≤ k T + B` for all `k ≥ 1` with `B` finite gives `I ≤ T`. -/
theorem le_of_forall_nat_mul_le {I T B : ℝ≥0∞} (hB : B ≠ ⊤)
    (h : ∀ k : ℕ, 0 < k → (k : ℝ≥0∞) * I ≤ k * T + B) : I ≤ T := by
  have h' : ∀ k : ℕ, 1 ≤ k → I ≤ T + B * (k : ℝ≥0∞)⁻¹ := fun k hk => by
    have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hk)
    have hkt : (k : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top k
    rw [← ENNReal.mul_le_mul_iff_right hk0 hkt, mul_add, mul_comm B, ← mul_assoc,
      ENNReal.mul_inv_cancel hk0 hkt, one_mul]
    exact h k hk
  have ht : Filter.Tendsto (fun k : ℕ => T + B * (k : ℝ≥0∞)⁻¹) Filter.atTop
      (nhds (T + B * 0)) :=
    tendsto_const_nhds.add
      (ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hB))
  rw [mul_zero, add_zero] at ht
  exact ge_of_tendsto ht (Filter.eventually_atTop.2 ⟨1, h'⟩)

/-! ### The pattern of stars and copies -/

open Classical in
/-- The roots of the patterns `P i`. -/
noncomputable def allRoots {r : ℕ} (P : Fin r → Pattern V) : Finset V :=
  Finset.univ.biUnion fun i => (P i).R

open Classical in
/-- The pattern made of the stars from the roots `y ∈ X` to `a y 0, …, a y (L - 1)` and
the copies `φ j` of the patterns `P j.1`, with the roots in `X` and `W` as new vertices
and the roots in `M` as roots. -/
noncomputable def starCopy {r : ℕ} (P : Fin r → Pattern V) {m : Fin r → ℕ}
    (φ : (Σ i, Fin (m i)) → V → V) (M X : Set V) (W : Finset V) (a : V → ℕ → V)
    (L : ℕ) :
    Pattern V where
  R := (allRoots P).filter (· ∈ M) ∪
    ((allRoots P).filter (· ∈ X)).biUnion fun y => (Finset.range L).image (a y)
  S := (allRoots P).filter (· ∈ X) ∪ W ∪ Finset.univ.biUnion fun j => (P j.1).S.image (φ j)
  E := ((allRoots P).filter (· ∈ X)).biUnion
      (fun y => (Finset.range L).image fun n => s(y, a y n)) ∪
    Finset.univ.biUnion fun j => (P j.1).E.image (Sym2.map (φ j))

open Classical in
/-- The stars and copies form a pattern over `M`. -/
theorem starCopy_isOver {G : SimpleGraph V} {C : ℝ≥0} {M N X : Set V}
    {ν : Measure (V → Bool)} (hX : X ⊆ N \ M) (d : ForcingData G C M X ν) {r : ℕ}
    {P : Fin r → Pattern V} (hP : ∀ i, (P i).IsOver G N) {W : Finset V}
    (hW : ∀ i, ∀ v ∈ (P i).R, v ∈ M ∨ v ∈ X ∨ v ∈ W) (hWN : ↑W ⊆ N \ M)
    {m : Fin r → ℕ} {φ : (Σ i, Fin (m i)) → V → V} {D : Finset V}
    (hφ : ∀ j, IsCopy G M N D (P j.1) (φ j)) (L : ℕ) :
    (starCopy P φ M X W d.a L).IsOver G M where
  roots_subset := by
    intro v hv
    simp only [Finset.mem_coe, starCopy, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image] at hv
    rcases hv with ⟨_, hv⟩ | ⟨y, ⟨_, hy⟩, n, _, rfl⟩
    · exact hv
    · exact (d.adj_mem y hy n).2
  new_not_mem := by
    intro v hv
    simp only [starCopy, Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_image] at hv
    rcases hv with (⟨_, hv⟩ | hv) | ⟨j, u, hu, rfl⟩
    · exact (hX hv).2
    · exact (hWN hv).2
    · exact ((hφ j).mem u hu).2.1
  edges_subset := by
    intro e he
    simp only [Finset.mem_coe, starCopy, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at he
    rcases he with ⟨y, ⟨_, hy⟩, n, _, rfl⟩ | ⟨j, e₀, he₀, rfl⟩
    · exact (d.adj_mem y hy n).1
    · exact (hφ j).edges e₀ he₀
  edges_meet := by
    intro e he
    simp only [starCopy, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image, Finset.mem_univ, true_and] at he
    rcases he with ⟨y, ⟨hyR, hy⟩, n, _, rfl⟩ | ⟨j, e₀, he₀, rfl⟩
    · refine ⟨y, Sym2.mem_mk_left _ _, ?_⟩
      simp only [starCopy, Finset.mem_union, Finset.mem_filter]
      exact Or.inl (Or.inl ⟨hyR, hy⟩)
    · obtain ⟨v, hv, hvS⟩ := (hP j.1).edges_meet e₀ he₀
      refine ⟨φ j v, Sym2.mem_map.2 ⟨v, hv, rfl⟩, ?_⟩
      simp only [starCopy, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image]
      exact Or.inr ⟨j, v, hvS, rfl⟩
  edges_inside := by
    intro e he w hw
    simp only [starCopy, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range] at he ⊢
    rcases he with ⟨y, ⟨hyR, hy⟩, n, hn, rfl⟩ | ⟨j, e₀, he₀, rfl⟩
    · rcases Sym2.mem_iff.1 hw with rfl | rfl
      · exact Or.inr (Or.inl (Or.inl ⟨hyR, hy⟩))
      · exact Or.inl (Or.inr ⟨y, ⟨hyR, hy⟩, n, hn, rfl⟩)
    · obtain ⟨u, hu, rfl⟩ := Sym2.mem_map.1 hw
      rcases (hP j.1).edges_inside e₀ he₀ u hu with huR | huS
      · have huS : u ∉ (P j.1).S := fun huS =>
          (hP j.1).new_not_mem u huS ((hP j.1).roots_subset huR)
        rw [(hφ j).eq_self u huS]
        have hu' : u ∈ allRoots P := Finset.mem_biUnion.2 ⟨j.1, Finset.mem_univ _, huR⟩
        rcases hW j.1 u huR with huM | huX | huW
        · exact Or.inl (Or.inl ⟨hu', huM⟩)
        · exact Or.inr (Or.inl (Or.inl ⟨hu', huX⟩))
        · exact Or.inr (Or.inl (Or.inr huW))
      · exact Or.inr (Or.inr ⟨j, u, huS, rfl⟩)

open Classical in
/-- The stars and copies have at most `|R ∩ X| + |W| + ∑ m i |S i|` new vertices. -/
theorem card_starCopy_S_le {r : ℕ} (P : Fin r → Pattern V) {m : Fin r → ℕ}
    (φ : (Σ i, Fin (m i)) → V → V) (M X : Set V) (W : Finset V) (a : V → ℕ → V)
    (L : ℕ) :
    (starCopy P φ M X W a L).S.card ≤
      ((allRoots P).filter (· ∈ X)).card + W.card + ∑ i, m i * (P i).S.card := by
  calc (starCopy P φ M X W a L).S.card
      ≤ (((allRoots P).filter (· ∈ X)) ∪ W).card +
          (Finset.univ.biUnion fun j => (P j.1).S.image (φ j)).card :=
        Finset.card_union_le _ _
    _ ≤ ((allRoots P).filter (· ∈ X)).card + W.card +
          ∑ j : (Σ i, Fin (m i)), ((P j.1).S.image (φ j)).card :=
        add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le
    _ ≤ ((allRoots P).filter (· ∈ X)).card + W.card +
          ∑ j : (Σ i, Fin (m i)), (P j.1).S.card :=
        Nat.add_le_add_left (Finset.sum_le_sum fun j _ => Finset.card_image_le) _
    _ = _ := by rw [sum_sigma_fin_nat m fun i => (P i).S.card]

open Classical in
/-- The combinatorial lower bound: once `L` exceeds the disagreements along every `a y`
plus the total number of edges of the copies, the stars and copies cost at least `k` times
the optimal weighted cost of the patterns under the forced signs. -/
theorem le_extCost_starCopy {G : SimpleGraph V} {C : ℝ≥0} {M N X : Set V}
    {ν : Measure (V → Bool)} (hX : X ⊆ N \ M) (d : ForcingData G C M X ν) {r : ℕ}
    {P : Fin r → Pattern V} (hP : ∀ i, (P i).IsOver G N) {W : Finset V}
    (hW : ∀ i, ∀ v ∈ (P i).R, v ∈ M ∨ v ∈ X ∨ v ∈ W) (hWN : ↑W ⊆ N \ M)
    (ρ : Fin r → ℝ≥0) {k : ℝ≥0∞} {m : Fin r → ℕ}
    (hm : ∀ i, k * ρ i ≤ m i) {φ : (Σ i, Fin (m i)) → V → V} {D : Finset V}
    (hRD : allRoots P ⊆ D) (hφ : ∀ j, IsCopy G M N D (P j.1) (φ j))
    (hdisj : ∀ j j', j ≠ j' → ∀ v ∈ (P j.1).S, ∀ v' ∈ (P j'.1).S, φ j v ≠ φ j' v')
    {ω : V → Bool}
    (hfin : ∀ y ∈ (allRoots P).filter (· ∈ X), {n | ω (d.a y n) ≠ d.s y ω}.Finite)
    {L : ℕ}
    (hL : ∑ y ∈ (allRoots P).filter (· ∈ X), {n | ω (d.a y n) ≠ d.s y ω}.ncard +
      ∑ j : (Σ i, Fin (m i)), (P j.1).E.card ≤ L) :
    k * ⨅ η : V → Bool, ∑ i, (ρ i : ℝ≥0∞) *
        extCost (P i).S (P i).E (W.piecewise η (forced X d.s ω)) ≤
      extCost (starCopy P φ M X W d.a L).S (starCopy P φ M X W d.a L).E ω := by
  set Q := starCopy P φ M X W d.a L with hQ
  have hQo : Q.IsOver G M := starCopy_isOver hX d hP hW hWN hφ L
  have hRP : ∀ i, (P i).R ⊆ D := fun i v hv =>
    hRD (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hv⟩)
  have hRS : ∀ i, ∀ v ∈ (P i).R, v ∉ (P i).S := fun i v hv hvS =>
    (hP i).new_not_mem v hvS ((hP i).roots_subset hv)
  obtain ⟨η, hη⟩ := exists_extCost_eq Q.S Q.E ω
  rw [← hη]
  set τ := Q.S.piecewise η ω with hτ
  -- the edges of the copies
  have hcopy : ∑ j, monoCount ((P j.1).E.image (Sym2.map (φ j))) τ ≤ monoCount Q.E τ := by
    rw [← monoCount_biUnion_of_pairwiseDisjoint]
    · exact monoCount_le_of_subset Finset.subset_union_right τ
    · intro j _ j' _ hne
      exact (hφ j).disjoint_edges (hφ j') (hP j.1) (hP j'.1) (hRP j'.1) (hdisj j j' hne)
  -- the signs off the new vertices
  have hτM : ∀ v ∈ M, τ v = ω v := fun v hv =>
    Finset.piecewise_eq_of_notMem _ _ _ fun hvS => hQo.new_not_mem v hvS hv
  by_cases hA : ∀ y ∈ (allRoots P).filter (· ∈ X), τ y = !d.s y ω
  · set τ₀ := W.piecewise τ (forced X d.s ω)
    have hagree : ∀ i, ∀ v ∈ (P i).R, τ v = τ₀ v := by
      intro i v hv
      by_cases hvW : v ∈ W
      · exact (Finset.piecewise_eq_of_mem _ _ _ hvW).symm
      rw [show τ₀ v = forced X d.s ω v from Finset.piecewise_eq_of_notMem _ _ _ hvW]
      have hvR : v ∈ allRoots P := Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hv⟩
      by_cases hvX : v ∈ X
      · rw [hA v (Finset.mem_filter.2 ⟨hvR, hvX⟩)]
        simp [forced, hvX]
      · have hvM : v ∈ M := by
          rcases hW i v hv with h | h | h
          · exact h
          · exact absurd h hvX
          · exact absurd h hvW
        rw [hτM v hvM]
        simp [forced, hvX]
    calc k * ⨅ η : V → Bool, ∑ i, (ρ i : ℝ≥0∞) *
          extCost (P i).S (P i).E (W.piecewise η (forced X d.s ω))
        ≤ k * ∑ i, (ρ i : ℝ≥0∞) * extCost (P i).S (P i).E τ₀ := by
          gcongr
          exact iInf_le _ τ
      _ = ∑ i, k * ρ i * extCost (P i).S (P i).E τ₀ := by
          rw [Finset.mul_sum]
          simp_rw [mul_assoc]
      _ ≤ ∑ i, (m i : ℝ≥0∞) * extCost (P i).S (P i).E τ₀ := by
          gcongr with i
          exact hm i
      _ = ∑ j : (Σ i, Fin (m i)), (extCost (P j.1).S (P j.1).E τ₀ : ℝ≥0∞) :=
          (sum_sigma_fin m _).symm
      _ ≤ ∑ j : (Σ i, Fin (m i)),
          (monoCount ((P j.1).E.image (Sym2.map (φ j))) τ : ℝ≥0∞) := by
          gcongr with j
          exact_mod_cast (hφ j).extCost_le_monoCount (hRP j.1) (hRS j.1)
            (hP j.1).edges_inside (hagree j.1)
      _ ≤ monoCount Q.E τ := by exact_mod_cast hcopy
  · push Not at hA
    obtain ⟨y, hy, hyτ⟩ := hA
    have hyτ' : τ y = d.s y ω := by simpa using hyτ
    obtain ⟨hyR, hyX⟩ := Finset.mem_filter.1 hy
    -- the star of `y`
    let A := (Finset.range L).filter fun n => ω (d.a y n) = d.s y ω
    have hstar : A.card ≤ monoCount Q.E τ := by
      calc A.card = (A.image fun n => s(y, d.a y n)).card := by
            rw [Finset.card_image_of_injective]
            intro n n' h
            exact d.injective y hyX (Sym2.congr_right.1 h)
        _ ≤ monoCount Q.E τ := by
            unfold monoCount
            apply Finset.card_le_card
            intro e he
            obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 he
            obtain ⟨hnL, hn⟩ := Finset.mem_filter.1 hn
            refine Finset.mem_filter.2 ⟨?_, ?_⟩
            · simp only [hQ, starCopy, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
              exact Or.inl ⟨y, hy, n, hnL, rfl⟩
            · change τ y = τ (d.a y n)
              rw [hyτ', hτM _ (d.adj_mem y hyX n).2, hn]
    have hbad : ((Finset.range L).filter fun n => ¬ω (d.a y n) = d.s y ω).card ≤
        {n | ω (d.a y n) ≠ d.s y ω}.ncard := by
      rw [← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard (fun n hn => ?_) (hfin y hy)
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn
      exact hn.2
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.range L) (fun n => ω (d.a y n) = d.s y ω)
    rw [Finset.card_range] at hsplit
    have hle := Finset.single_le_sum (f := fun y => {n | ω (d.a y n) ≠ d.s y ω}.ncard)
      (fun _ _ => Nat.zero_le _) hy
    have hEA : ∑ j : (Σ i, Fin (m i)), (P j.1).E.card ≤ A.card := by
      change _ ≤ ((Finset.range L).filter fun n => ω (d.a y n) = d.s y ω).card
      omega
    calc k * ⨅ η : V → Bool, ∑ i, (ρ i : ℝ≥0∞) *
          extCost (P i).S (P i).E (W.piecewise η (forced X d.s ω))
        ≤ k * ∑ i, (ρ i : ℝ≥0∞) * (P i).E.card := by
          gcongr
          refine (iInf_le _ ω).trans ?_
          gcongr with i
          exact_mod_cast extCost_le_card _ _ _
      _ = ∑ i, k * ρ i * (P i).E.card := by
          rw [Finset.mul_sum]
          simp_rw [mul_assoc]
      _ ≤ ∑ i, (m i : ℝ≥0∞) * (P i).E.card := by
          gcongr with i
          exact hm i
      _ = ∑ j : (Σ i, Fin (m i)), ((P j.1).E.card : ℝ≥0∞) := (sum_sigma_fin m _).symm
      _ ≤ monoCount Q.E τ := by exact_mod_cast hEA.trans hstar

open Classical in
/-- The key inequality (S) of the successor step, for nonnegative real weights. -/
theorem key_inequality {G : SimpleGraph V} {C : ℝ≥0} {M N X : Set V}
    (hMN : ClosedOver G M N) {ν : Measure (V → Bool)}
    (hν : Rooted G C M ν) (hX : X ⊆ N \ M) (d : ForcingData G C M X ν)
    {r : ℕ} (P : Fin r → Pattern V) (hP : ∀ i, (P i).IsOver G N) (W : Finset V)
    (hW : ∀ i, ∀ v ∈ (P i).R, v ∈ M ∨ v ∈ X ∨ v ∈ W) (hWN : ↑W ⊆ N \ M)
    (ρ : Fin r → ℝ≥0) :
    ∫⁻ ω, ⨅ η : V → Bool, ∑ i, (ρ i : ℝ≥0∞) *
        extCost (P i).S (P i).E (W.piecewise η (forced X d.s ω)) ∂ν ≤
      ∑ i, (ρ i : ℝ≥0∞) * (C * (P i).S.card) := by
  set Rx := (allRoots P).filter (· ∈ X)
  set F : (V → Bool) → ℝ≥0∞ := fun ω => ⨅ η : V → Bool, ∑ i, (ρ i : ℝ≥0∞) *
    extCost (P i).S (P i).E (W.piecewise η (forced X d.s ω))
  refine le_of_forall_nat_mul_le
    (B := (C : ℝ≥0∞) * ((Rx.card + W.card + ∑ i, (P i).S.card : ℕ) : ℝ≥0∞))
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.natCast_ne_top _)) fun k _ => ?_
  -- the numbers of copies
  let m : Fin r → ℕ := fun i => ⌈(k : ℝ≥0) * ρ i⌉₊
  have hm : ∀ i, (k : ℝ≥0∞) * ρ i ≤ m i := fun i => by
    have := Nat.le_ceil ((k : ℝ≥0) * ρ i)
    exact_mod_cast this
  have hm' : ∀ i, (m i : ℝ≥0∞) ≤ k * ρ i + 1 := fun i => by
    have := Nat.ceil_lt_add_one (zero_le (a := (k : ℝ≥0) * ρ i))
    exact_mod_cast this.le
  -- the copies, avoiding all roots
  obtain ⟨φ, hφ, hdisj⟩ := exists_copies hMN (fun j : (Σ i, Fin (m i)) => P j.1)
    (fun j => hP j.1) (D := allRoots P) (by
      intro v hv
      obtain ⟨i, _, hv⟩ := Finset.mem_biUnion.1 hv
      exact (hP i).roots_subset hv)
  have hQo := fun L => starCopy_isOver hX d hP hW hWN hφ L
  have hmeas : ∀ L, Measurable fun ω =>
      (extCost (starCopy P φ M X W d.a L).S (starCopy P φ M X W d.a L).E ω : ℝ≥0∞) :=
    fun L => measurable_from_nat.comp
      (measurable_of_dependsOn (extCost_dependsOn (hQo L).edges_inside))
  -- the pointwise lower bound, almost surely
  have hae : ∀ᵐ ω ∂ν, (k : ℝ≥0∞) * F ω ≤ Filter.liminf (fun L =>
      (extCost (starCopy P φ M X W d.a L).S (starCopy P φ M X W d.a L).E ω : ℝ≥0∞))
      Filter.atTop := by
    have hfin : ∀ᵐ ω ∂ν, ∀ y ∈ Rx, {n | ω (d.a y n) ≠ d.s y ω}.Finite :=
      (Filter.eventually_all_finset Rx).2 fun y hy => d.ae_finite y (Finset.mem_filter.1 hy).2
    filter_upwards [hfin] with ω hω
    exact Filter.le_liminf_of_le (by isBoundedDefault) (Filter.eventually_atTop.2
      ⟨_, fun L hL => le_extCost_starCopy hX d hP hW hWN ρ hm (Finset.Subset.refl _) hφ hdisj
        hω hL⟩)
  -- the size of the new vertices
  have hcard : ∀ L, (C : ℝ≥0∞) * (starCopy P φ M X W d.a L).S.card ≤
      C * ((Rx.card + W.card + ∑ i, m i * (P i).S.card : ℕ) : ℝ≥0∞) := fun L => by
    gcongr
    exact_mod_cast card_starCopy_S_le P φ M X W d.a L
  calc (k : ℝ≥0∞) * ∫⁻ ω, F ω ∂ν
      ≤ ∫⁻ ω, k * F ω ∂ν := lintegral_const_mul_le _ _
    _ ≤ ∫⁻ ω, Filter.liminf (fun L =>
          (extCost (starCopy P φ M X W d.a L).S (starCopy P φ M X W d.a L).E ω : ℝ≥0∞))
          Filter.atTop ∂ν := lintegral_mono_ae hae
    _ ≤ Filter.liminf (fun L => ∫⁻ ω, (extCost (starCopy P φ M X W d.a L).S
          (starCopy P φ M X W d.a L).E ω : ℝ≥0∞) ∂ν)
          Filter.atTop := lintegral_liminf_le hmeas
    _ ≤ C * ((Rx.card + W.card + ∑ i, m i * (P i).S.card : ℕ) : ℝ≥0∞) :=
        Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun L =>
          (hν _ (hQo L)).trans (hcard L))
    _ ≤ C * ((Rx.card + W.card : ℕ) + ∑ i, ((k : ℝ≥0∞) * ρ i + 1) * (P i).S.card) := by
        push_cast
        gcongr with i
        exact hm' i
    _ = k * ∑ i, (ρ i : ℝ≥0∞) * (C * (P i).S.card) +
          C * ((Rx.card + W.card + ∑ i, (P i).S.card : ℕ) : ℝ≥0∞) := by
        have h1 : ∑ i, ((k : ℝ≥0∞) * ρ i + 1) * (P i).S.card =
            k * ∑ i, (ρ i : ℝ≥0∞) * (P i).S.card + ∑ i, ((P i).S.card : ℝ≥0∞) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        have h2 : ∑ i, (ρ i : ℝ≥0∞) * (C * (P i).S.card) =
            C * ∑ i, (ρ i : ℝ≥0∞) * (P i).S.card := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [h1, h2]
        push_cast
        ring

end Erdos111
