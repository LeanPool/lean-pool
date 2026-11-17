/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.ClassicalMatchingFactors.Regular.BalancedOrientation
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Set.Card

/-!

Imported from [jtraverso/euler-petersen](https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Petersen.lean), registered as PALOMAR-2026-10-16-000016. The original proof is retained; module paths and imports are adapted for this collection.

# Teorema del 2-factor de Petersen (1891)

Todo grafo finito `2k`-regular es unión disjunta (en aristas) de `k` 2-factores, es decir, de `k`
subgrafos generadores en los que cada vértice tiene grado exactamente `2`.

Prueba clásica:
1. **Euler**: por la orientación euleriana (`exists_balanced_orientation`, que descompone el grafo
   en trails cerrados), cada vértice tiene `k` arcos salientes y `k` entrantes.
2. **Hall**: un digrafo con `k ≥ 1` arcos salientes y entrantes en cada vértice contiene una
   permutación `σ` (es decir, `v → σ v` es un arco para todo `v`); quitándola queda un digrafo
   `(k-1)`-regular, y así los arcos se parten en `k` permutaciones.
3. Cada permutación `σ` da un 2-factor: los vecinos de `v` son `σ v` y `σ⁻¹ v`, distintos porque
   la orientación nunca contiene a la vez `v → w` y `w → v`.

Referencia: J. Petersen, *Die Theorie der regulären graphs*, Acta Math. 15 (1891) 193–220.
-/

@[expose] public section

namespace SimpleGraph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Permutaciones en digrafos regulares (Hall) -/

omit [Fintype V] in
/-- **Hall para digrafos regulares.** Si cada vértice tiene `k ≥ 1` arcos salientes y `k`
entrantes en `D`, existe una permutación `σ` con `(v, σ v) ∈ D` para todo `v`. -/
theorem exists_perm_subset [Finite V] {D : Finset (V × V)} {k : ℕ} (hk : 0 < k)
    (hout : ∀ v, (D.filter fun p => p.1 = v).card = k)
    (hin : ∀ v, (D.filter fun p => p.2 = v).card = k) :
    ∃ σ : Equiv.Perm V, ∀ v, (v, σ v) ∈ D := by
  let := Fintype.ofFinite V
  set t : V → Finset V := fun u => (D.filter fun p => p.1 = u).image Prod.snd
  have hall : ∀ s : Finset V, s.card ≤ (s.biUnion t).card := by
    intro s
    -- arcos que salen de `s`
    have h1 : (D.filter fun p => p.1 ∈ s).card = k * s.card := by
      have : (D.filter fun p => p.1 ∈ s) = s.biUnion fun u => D.filter fun p => p.1 = u := by
        ext p; simp only [mem_filter, mem_biUnion]
        constructor
        · rintro ⟨hp, hs⟩; exact ⟨p.1, hs, hp, rfl⟩
        · rintro ⟨u, hu, hp, rfl⟩; exact ⟨hp, hu⟩
      rw [this, card_biUnion fun x _ y _ hxy => disjoint_filter.mpr fun p _ h1 h2 =>
        hxy (h1.symm.trans h2)]
      rw [Finset.sum_congr rfl fun u _ => hout u, sum_const, smul_eq_mul, Nat.mul_comm]
    -- llegan a `N(s)`
    have h2 : (D.filter fun p => p.2 ∈ s.biUnion t).card = k * (s.biUnion t).card := by
      have : (D.filter fun p => p.2 ∈ s.biUnion t) =
          (s.biUnion t).biUnion fun w => D.filter fun p => p.2 = w := by
        ext p; simp only [mem_filter, mem_biUnion]
        constructor
        · rintro ⟨hp, hs⟩; exact ⟨p.2, hs, hp, rfl⟩
        · rintro ⟨w, hw, hp, rfl⟩; exact ⟨hp, hw⟩
      rw [this, card_biUnion fun x _ y _ hxy => disjoint_filter.mpr fun p _ h1 h2 =>
        hxy (h1.symm.trans h2)]
      rw [Finset.sum_congr rfl fun w _ => hin w, sum_const, smul_eq_mul, Nat.mul_comm]
    have h3 : (D.filter fun p => p.1 ∈ s) ⊆ D.filter fun p => p.2 ∈ s.biUnion t := by
      intro p hp
      obtain ⟨hpD, hps⟩ := mem_filter.mp hp
      refine mem_filter.mpr ⟨hpD, mem_biUnion.mpr ⟨p.1, hps, ?_⟩⟩
      exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hpD, rfl⟩, rfl⟩
    have := card_le_card h3
    rw [h1, h2] at this
    exact Nat.le_of_mul_le_mul_left this hk
  obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hf
  refine ⟨Equiv.ofBijective f hbij, fun v => ?_⟩
  obtain ⟨p, hp, hpv⟩ := mem_image.mp (hft v)
  obtain ⟨hpD, hp1⟩ := mem_filter.mp hp
  have : p = (v, f v) := Prod.ext hp1 hpv
  simpa [this] using hpD

omit [Fintype V] in
/-- **Descomposición en permutaciones.** Un digrafo `k`-regular (de entrada y salida) se parte
en `k` permutaciones con arcos disjuntos. -/
theorem exists_perm_decomp [Finite V] : ∀ (k : ℕ) (D : Finset (V × V)),
    (∀ v, (D.filter fun p => p.1 = v).card = k) → (∀ v, (D.filter fun p => p.2 = v).card = k) →
    ∃ σ : Fin k → Equiv.Perm V, (∀ i v, (v, σ i v) ∈ D) ∧
      (∀ i j v, σ i v = σ j v → i = j) ∧ (∀ p ∈ D, ∃ i, σ i p.1 = p.2) := by
  intro k
  let := Fintype.ofFinite V
  induction k with
  | zero =>
    intro D hout _
    refine ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun p hp => ?_⟩
    have := hout p.1
    rw [card_eq_zero] at this
    have hmem : p ∈ D.filter (fun q => q.1 = p.1) := mem_filter.mpr ⟨hp, rfl⟩
    rw [this] at hmem
    exact absurd hmem (notMem_empty _)
  | succ k ih =>
    intro D hout hin
    obtain ⟨σ₀, hσ₀⟩ := exists_perm_subset (Nat.succ_pos k) hout hin
    set M := univ.image fun v => (v, σ₀ v)
    set D' := D \ M
    have hM : ∀ p, p ∈ M ↔ σ₀ p.1 = p.2 := by
      intro p
      simp only [M, mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨v, rfl⟩; rfl
      · intro h; exact ⟨p.1, Prod.ext rfl h⟩
    have hout' : ∀ v, (D'.filter fun p => p.1 = v).card = k := by
      intro v
      have : D'.filter (fun p => p.1 = v) = (D.filter fun p => p.1 = v).erase (v, σ₀ v) := by
        ext p
        simp only [D', mem_filter, mem_sdiff, mem_erase, hM]
        constructor
        · rintro ⟨⟨hpD, hpM⟩, rfl⟩
          exact ⟨fun h => hpM (by rw [h]), hpD, rfl⟩
        · rintro ⟨hne, hpD, rfl⟩
          exact ⟨⟨hpD, fun h => hne (Prod.ext rfl h.symm)⟩, rfl⟩
      have hm : (v, σ₀ v) ∈ D.filter (fun p => p.1 = v) := mem_filter.mpr ⟨hσ₀ v, rfl⟩
      rw [this, card_erase_of_mem hm, hout v]
      rfl
    have hin' : ∀ w, (D'.filter fun p => p.2 = w).card = k := by
      intro w
      have : D'.filter (fun p => p.2 = w) =
          (D.filter fun p => p.2 = w).erase (σ₀.symm w, w) := by
        ext p
        simp only [D', mem_filter, mem_sdiff, mem_erase, hM]
        constructor
        · rintro ⟨⟨hpD, hpM⟩, rfl⟩
          refine ⟨fun h => hpM ?_, hpD, rfl⟩
          rw [h]; simp
        · rintro ⟨hne, hpD, rfl⟩
          refine ⟨⟨hpD, fun h => hne (Prod.ext ?_ rfl)⟩, rfl⟩
          rw [← h]; simp
      have hm : (σ₀.symm w, w) ∈ D.filter (fun p => p.2 = w) :=
        mem_filter.mpr ⟨by simpa using hσ₀ (σ₀.symm w), rfl⟩
      rw [this, card_erase_of_mem hm, hin w]
      rfl
    obtain ⟨τ, hτD, hτdisj, hτcov⟩ := ih D' hout' hin'
    refine ⟨Fin.cons σ₀ τ, fun i v => ?_, fun i j v hij => ?_, fun p hp => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact hσ₀ v
      · exact (mem_sdiff.mp (hτD j v)).1
    · have hnot : ∀ j v, τ j v ≠ σ₀ v := by
        intro j v h
        exact (mem_sdiff.mp (hτD j v)).2 ((hM _).mpr h.symm)
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => rfl
        | succ j => exact absurd hij.symm (by simpa using hnot j v)
      | succ i =>
        induction j using Fin.cases with
        | zero => exact absurd hij (by simpa using hnot i v)
        | succ j => simp only [Fin.cons_succ] at hij; rw [hτdisj i j v hij]
    · by_cases hpM : p ∈ M
      · exact ⟨0, by simpa using (hM p).mp hpM⟩
      · obtain ⟨j, hj⟩ := hτcov p (mem_sdiff.mpr ⟨hp, hpM⟩)
        exact ⟨j.succ, by simpa using hj⟩

/-! ### Los 2-factores -/

/-- El 2-factor asociado a una permutación: `u ∼ w` si `σ u = w` o `σ w = u`. -/
def permGraph (σ : Equiv.Perm V) : SimpleGraph V where
  Adj u w := u ≠ w ∧ (σ u = w ∨ σ w = u)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- **Teorema del 2-factor de Petersen.** Todo grafo finito `2k`-regular se descompone en `k`
2-factores disjuntos en aristas. -/
theorem petersen_two_factor (k : ℕ) (h : ∀ v, G.degree v = 2 * k) :
    ∃ F : Fin k → SimpleGraph V, (∀ i, F i ≤ G) ∧
      (∀ i v, ((F i).neighborSet v).ncard = 2) ∧
      (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧ ⨆ i, F i = G := by
  classical
  obtain ⟨Ds, hinj, hbal, hcov⟩ :=
    exists_balanced_orientation (G := G) fun v => ⟨k, by rw [h v]; omega⟩
  set D := Ds.image Dart.toProd
  have hDmem : ∀ p, p ∈ D ↔ ∃ d ∈ Ds, d.toProd = p := fun p => by simp [D]
  have htoProd_inj : ∀ d ∈ Ds, ∀ d' ∈ Ds, d.toProd = d'.toProd → d = d' :=
    fun d _ d' _ h => (Dart.ext_iff d d').mpr h
  -- grados de salida y de entrada
  have hsum : ∀ v, (Ds.filter fun d => d.fst = v).card + (Ds.filter fun d => d.snd = v).card =
      2 * k := by
    intro v
    rw [← card_image_edge_filter hinj, ← h v, ← card_incidenceFinset_eq_degree]
    congr 1
    ext e
    simp only [mem_filter, mem_image, mem_incidenceFinset, incidenceSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨d, -, rfl⟩, hv⟩; exact ⟨d.edge_mem, hv⟩
    · rintro ⟨he, hv⟩; obtain ⟨d, hd, rfl⟩ := hcov e he; exact ⟨⟨d, hd, rfl⟩, hv⟩
  have hfilter1 : ∀ v, (D.filter fun p => p.1 = v).card = (Ds.filter fun d => d.fst = v).card := by
    intro v
    rw [show D.filter (fun p => p.1 = v) = (Ds.filter fun d => d.fst = v).image Dart.toProd by
      ext p; simp only [D, mem_filter, mem_image, and_comm]; constructor
      · rintro ⟨h1, a, rfl, ha⟩; exact ⟨a, rfl, h1, ha⟩
      · rintro ⟨a, rfl, h1, ha⟩; exact ⟨h1, a, rfl, ha⟩, card_image_of_injOn fun d hd d' hd' =>
        htoProd_inj d (mem_filter.mp hd).1 d' (mem_filter.mp hd').1]
  have hfilter2 : ∀ v, (D.filter fun p => p.2 = v).card = (Ds.filter fun d => d.snd = v).card := by
    intro v
    rw [show D.filter (fun p => p.2 = v) = (Ds.filter fun d => d.snd = v).image Dart.toProd by
      ext p; simp only [D, mem_filter, mem_image, and_comm]; constructor
      · rintro ⟨h1, a, rfl, ha⟩; exact ⟨a, rfl, h1, ha⟩
      · rintro ⟨a, rfl, h1, ha⟩; exact ⟨h1, a, rfl, ha⟩, card_image_of_injOn fun d hd d' hd' =>
        htoProd_inj d (mem_filter.mp hd).1 d' (mem_filter.mp hd').1]
  have hout : ∀ v, (D.filter fun p => p.1 = v).card = k := by
    intro v; have := hsum v; have := hbal v; rw [hfilter1]; omega
  have hin : ∀ v, (D.filter fun p => p.2 = v).card = k := by
    intro v; have := hsum v; have := hbal v; rw [hfilter2]; omega
  obtain ⟨σ, hσD, hσdisj, hσcov⟩ := exists_perm_decomp k D hout hin
  -- propiedades de `D`
  have hDadj : ∀ u w, (u, w) ∈ D → G.Adj u w := by
    intro u w huw
    obtain ⟨d, -, hd⟩ := (hDmem _).mp huw
    have := d.adj
    rw [show d.fst = u from congrArg Prod.fst hd, show d.snd = w from congrArg Prod.snd hd] at this
    exact this
  have hDanti : ∀ u w, (u, w) ∈ D → (w, u) ∉ D := by
    intro u w huw hwu
    obtain ⟨d, hd, hdp⟩ := (hDmem _).mp huw
    obtain ⟨d', hd', hdp'⟩ := (hDmem _).mp hwu
    have he : d.edge = d'.edge := by
      rw [Dart.edge, Dart.edge, hdp, hdp']; exact Sym2.eq_swap
    have := hinj d hd d' hd' he
    subst this
    have h1 := congrArg Prod.fst (hdp.symm.trans hdp')
    exact (hDadj u w huw).ne h1
  refine ⟨fun i => permGraph (σ i), fun i u w huw => ?_, fun i v => ?_, fun i j hij => ?_, ?_⟩
  · rcases huw.2 with h | h
    · exact h ▸ hDadj _ _ (hσD i u)
    · exact (h ▸ hDadj _ _ (hσD i w)).symm
  · have hne1 : σ i v ≠ v := fun h' => (hDadj _ _ (hσD i v)).ne h'.symm
    have hne2 : (σ i).symm v ≠ v := by
      intro h'
      have := hDadj _ _ (hσD i ((σ i).symm v))
      rw [Equiv.apply_symm_apply, h'] at this
      exact G.loopless.irrefl _ this
    have hset : (permGraph (σ i)).neighborSet v = {σ i v, (σ i).symm v} := by
      ext w
      simp only [mem_neighborSet, permGraph, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨-, h' | h'⟩
        · exact Or.inl h'.symm
        · right; rw [← h']; simp
      · rintro (rfl | rfl)
        · exact ⟨hne1.symm, Or.inl rfl⟩
        · exact ⟨hne2.symm, Or.inr (by simp)⟩
    rw [hset, Set.ncard_pair]
    intro heq
    have h1 := hσD i v
    have h2 := hσD i (σ i v)
    have : σ i (σ i v) = v := by
      conv_rhs => rw [← Equiv.apply_symm_apply (σ i) v]
      rw [← heq]
    rw [this] at h2
    exact hDanti _ _ h1 h2
  · rw [disjoint_iff_inf_le]
    intro u w ⟨hi, hj⟩
    exfalso
    rcases hi.2 with h1 | h1 <;> rcases hj.2 with h2 | h2
    · exact hij (hσdisj i j u (h1.trans h2.symm))
    · exact hDanti _ _ (h1 ▸ hσD i u) (h2 ▸ hσD j w)
    · exact hDanti _ _ (h1 ▸ hσD i w) (h2 ▸ hσD j u)
    · exact hij (hσdisj i j w (h1.trans h2.symm))
  · ext u w
    rw [iSup_adj]
    constructor
    · rintro ⟨i, hi⟩
      rcases hi.2 with h' | h'
      · exact h' ▸ hDadj _ _ (hσD i u)
      · exact (h' ▸ hDadj _ _ (hσD i w)).symm
    · intro huw
      obtain ⟨d, hd, hde⟩ := hcov s(u, w) huw
      have hdD : d.toProd ∈ D := mem_image_of_mem _ hd
      obtain ⟨i, hi⟩ := hσcov _ hdD
      refine ⟨i, huw.ne, ?_⟩
      rcases Sym2.eq_iff.mp hde with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [← h1, ← h2]; exact hi
      · right; rw [← h1, ← h2]; exact hi

end SimpleGraph
