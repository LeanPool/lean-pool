/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Tactic

/-!
# Spectral bounds on the chromatic number and the independence number

Let `G` be a finite simple graph on a nonempty vertex type, `A` its real adjacency matrix
(Mathlib's `SimpleGraph.adjMatrix`), which is Hermitian, and `λ_max`, `λ_min` its largest and
smallest eigenvalues (`Matrix.IsHermitian.eigenvalues`).

* `SpectralBounds.average_degree_le` and `SpectralBounds.le_maxDegree`: the average degree
  `2|E|/n` is at most `λ_max`, and `λ_max` is at most the maximum degree.
* `SpectralBounds.wilf`: **Wilf (1967).** `G` is `(⌊λ_max⌋ + 1)`-colourable.
* `SpectralBounds.hoffman_chromatic`: **Hoffman (1970).** If `G` has an edge, every proper
  colouring uses at least `1 - λ_max / λ_min` colours.
* `SpectralBounds.hoffman_ratio`: **Hoffman's ratio bound.** If `G` is `k`-regular with `k ≥ 1`,
  every independent set has at most `n (−λ_min) / (k − λ_min)` vertices.
-/

@[expose] public section

open Finset SimpleGraph

namespace SpectralBounds

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)

section Spectral

variable {W : Type*} [Fintype W] [DecidableEq W] {M : Matrix W W ℝ}

open Matrix

/-- Expansion of the quadratic form of a real symmetric matrix in an orthonormal eigenbasis. -/
theorem exists_quadForm_eq (hM : M.IsHermitian) (x : W → ℝ) :
    ∃ y : W → ℝ, x ⬝ᵥ (M *ᵥ x) = ∑ i, hM.eigenvalues i * y i ^ 2 ∧
      x ⬝ᵥ x = ∑ i, y i ^ 2 := by
  set U : Matrix W W ℝ := (hM.eigenvectorUnitary : Matrix W W ℝ) with hU
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hs : star U = Uᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  refine ⟨Uᵀ *ᵥ x, ?_, ?_⟩
  · conv_lhs => rw [hM.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    rw [← hU, hs, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
    simp [dotProduct, mulVec_diagonal, sq, mul_left_comm]
  · have : ∑ i, (Uᵀ *ᵥ x) i ^ 2 = (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ x) := by simp [dotProduct, sq]
    rw [this, dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, ← hs, hUU, one_mulVec,
      dotProduct_comm]

/-- Rayleigh upper bound: `xᵀ M x ≤ λ_max ‖x‖²`. -/
theorem quadForm_le_iSup (hM : M.IsHermitian) (x : W → ℝ) :
    x ⬝ᵥ (M *ᵥ x) ≤ (⨆ i, hM.eigenvalues i) * (x ⬝ᵥ x) := by
  obtain ⟨y, h1, h2⟩ := exists_quadForm_eq hM x
  rw [h1, h2, mul_sum]
  gcongr with i
  exact le_ciSup (Set.finite_range _).bddAbove i

/-- Rayleigh lower bound: `λ_min ‖x‖² ≤ xᵀ M x`. -/
theorem iInf_le_quadForm (hM : M.IsHermitian) (x : W → ℝ) :
    (⨅ i, hM.eigenvalues i) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (M *ᵥ x) := by
  obtain ⟨y, h1, h2⟩ := exists_quadForm_eq hM x
  rw [h1, h2, mul_sum]
  gcongr with i
  exact ciInf_le (Set.finite_range _).bddBelow i

/-- There is a unit eigenvector for the largest eigenvalue. -/
theorem exists_unit_eigenvector_iSup [Nonempty W] (hM : M.IsHermitian) :
    ∃ x : W → ℝ, M *ᵥ x = (⨆ i, hM.eigenvalues i) • x ∧ x ⬝ᵥ x = 1 := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := hM.eigenvalues)
  refine ⟨⇑(hM.eigenvectorBasis i), ?_, ?_⟩
  · rw [hM.mulVec_eigenvectorBasis, hi]
  · have h1 := hM.eigenvectorBasis.orthonormal.1 i
    have h2 := real_inner_self_eq_norm_sq (hM.eigenvectorBasis i)
    rw [h1, one_pow, EuclideanSpace.inner_eq_star_dotProduct] at h2
    simpa [dotProduct_comm] using h2

end Spectral

open Matrix

omit [DecidableEq V] [Nonempty V] in
/-- The quadratic form of the adjacency matrix vanishes on vectors supported on an
independent set. -/
theorem quadForm_eq_zero_of_indep (z : V → ℝ) (hz : ∀ u v, G.Adj u v → z u = 0 ∨ z v = 0) :
    z ⬝ᵥ (G.adjMatrix ℝ *ᵥ z) = 0 := by
  simp only [dotProduct, mulVec, mul_sum]
  refine sum_eq_zero fun v _ => sum_eq_zero fun u _ => ?_
  classical
  rw [adjMatrix_apply]
  split_ifs with h
  · rcases hz v u h with h | h <;> simp [h]
  · simp

omit [DecidableEq V] [Nonempty V] in
theorem dotProduct_adjMatrix_mulVec_comm (x z : V → ℝ) :
    x ⬝ᵥ (G.adjMatrix ℝ *ᵥ z) = z ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, transpose_adjMatrix, dotProduct_comm]

omit [Nonempty V] in
/-- The key inequality behind both Hoffman bounds: apply the Rayleigh lower bound to
`z - t • x`, where `x` is an eigenvector and `z` has vanishing quadratic form. -/
theorem hoffman_key (x z : V → ℝ) (θ t : ℝ) (hx : G.adjMatrix ℝ *ᵥ x = θ • x)
    (hz : z ⬝ᵥ (G.adjMatrix ℝ *ᵥ z) = 0) :
    (⨅ i, hA.eigenvalues i) * (z ⬝ᵥ z - 2 * t * (z ⬝ᵥ x) + t ^ 2 * (x ⬝ᵥ x)) ≤
      -2 * t * θ * (z ⬝ᵥ x) + t ^ 2 * θ * (x ⬝ᵥ x) := by
  have h := iInf_le_quadForm hA (z - t • x)
  have hxz : x ⬝ᵥ (G.adjMatrix ℝ *ᵥ z) = θ * (z ⬝ᵥ x) := by
    rw [dotProduct_adjMatrix_mulVec_comm, hx, dotProduct_smul, smul_eq_mul]
  have hzx : z ⬝ᵥ x = x ⬝ᵥ z := dotProduct_comm _ _
  simp only [mulVec_sub, mulVec_smul, hx, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hz] at h
  rw [hxz] at h
  rw [← hzx] at h
  nlinarith [h]

theorem iInf_eigenvalues_nonpos : (⨅ i, hA.eigenvalues i) ≤ 0 := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have h := iInf_le_quadForm hA (Pi.single v 1)
  simpa using h

omit [Nonempty V] in
theorem iInf_eigenvalues_le_neg_one (hE : G.edgeSet.Nonempty) :
    (⨅ i, hA.eigenvalues i) ≤ -1 := by
  obtain ⟨e, he⟩ := hE
  induction e using Sym2.ind with
  | _ u v =>
  rw [mem_edgeSet] at he
  have huv : u ≠ v := he.ne
  have h := iInf_le_quadForm hA (Pi.single u 1 - Pi.single v 1)
  simp [mulVec_sub, dotProduct_sub, sub_dotProduct, huv, huv.symm, he, he.symm] at h
  linarith

omit [Nonempty V] in
theorem exists_low_degree (S : Finset V) (hS : S.Nonempty) :
    ∃ v ∈ S, (#(G.neighborFinset v ∩ S) : ℝ) ≤ ⨆ i, hA.eigenvalues i := by
  set x : V → ℝ := fun w => if w ∈ S then 1 else 0
  have h := quadForm_le_iSup hA x
  have hxx : x ⬝ᵥ x = #S := by simp [x, dotProduct]
  have hq : x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) = ∑ v ∈ S, (#(G.neighborFinset v ∩ S) : ℝ) := by
    simp [x, dotProduct]
  rw [hxx, hq] at h
  refine exists_le_of_sum_le hS ?_
  simpa [mul_comm] using h

omit [Nonempty V] in
theorem exists_coloring_of_low_degree (m : ℕ)
    (h : ∀ S : Finset V, S.Nonempty → ∃ v ∈ S, #(G.neighborFinset v ∩ S) ≤ m)
    (S : Finset V) : ∃ f : V → Fin (m + 1), ∀ u ∈ S, ∀ w ∈ S, G.Adj u w → f u ≠ f w := by
  induction S using Finset.strongInduction with
  | H S ih =>
  rcases S.eq_empty_or_nonempty with rfl | hS
  · exact ⟨fun _ => 0, by simp⟩
  obtain ⟨v, hv, hdeg⟩ := h S hS
  obtain ⟨f, hf⟩ := ih (S.erase v) (erase_ssubset hv)
  have hcard : #(({u ∈ G.neighborFinset v | u ∈ S}).image f) < #(univ : Finset (Fin (m + 1))) :=
    by
      rw [card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt (card_image_le.trans hdeg) (Nat.lt_succ_self m)
  obtain ⟨c, -, hc⟩ := exists_mem_notMem_of_card_lt_card hcard
  refine ⟨Function.update f v c, fun u hu w hw huw => ?_⟩
  have key : ∀ y ∈ S, G.Adj v y → c ≠ f y := by
    intro y hy hvy hcy
    exact hc (mem_image.2 ⟨y, by simp [hy, hvy], hcy.symm⟩)
  by_cases huv : u = v
  · subst huv
    have hwv : w ≠ u := huw.ne.symm
    simpa [hwv] using key w hw huw
  by_cases hwv : w = v
  · subst hwv
    simpa [huv] using (key u hu huw.symm).symm
  simpa [huv, hwv] using hf u (mem_erase.2 ⟨huv, hu⟩) w (mem_erase.2 ⟨hwv, hw⟩) huw

/-- The average degree `2 |E| / n` is at most the largest adjacency eigenvalue. -/
theorem average_degree_le :
    2 * (#G.edgeFinset : ℝ) / Fintype.card V ≤ ⨆ i, hA.eigenvalues i := by
  have h := quadForm_le_iSup hA (fun _ : V => (1 : ℝ))
  have hxx : (fun _ : V => (1 : ℝ)) ⬝ᵥ (fun _ : V => (1 : ℝ)) = Fintype.card V := by
    simp [dotProduct]
  have hq : (fun _ : V => (1 : ℝ)) ⬝ᵥ (G.adjMatrix ℝ *ᵥ fun _ : V => (1 : ℝ)) =
      2 * (#G.edgeFinset : ℝ) := by
    simp only [dotProduct, adjMatrix_mulVec_apply, sum_const, one_mul,
      card_neighborFinset_eq_degree, nsmul_eq_mul, mul_one]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [hxx, hq] at h
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  rwa [div_le_iff₀ hn]

/-- The largest adjacency eigenvalue is at most the maximum degree. -/
theorem le_maxDegree : ⨆ i, hA.eigenvalues i ≤ G.maxDegree := by
  obtain ⟨x, hx, hxx⟩ := exists_unit_eigenvector_iSup hA
  set lam := ⨆ i, hA.eigenvalues i
  obtain ⟨u, -, hu⟩ := exists_max_image univ (fun v => |x v|) univ_nonempty
  have hpos : 0 < |x u| := by
    by_contra hneg
    have h0 : ∀ v, x v = 0 := fun v =>
      abs_eq_zero.1 (le_antisymm ((hu v (mem_univ v)).trans (not_lt.1 hneg)) (abs_nonneg _))
    simp [dotProduct, h0] at hxx
  have hxu : lam * x u = ∑ w ∈ G.neighborFinset u, x w := by
    rw [← adjMatrix_mulVec_apply, hx]
    simp
  have hbound : |lam| * |x u| ≤ G.maxDegree * |x u| := by
    rw [← abs_mul, hxu]
    calc |∑ w ∈ G.neighborFinset u, x w| ≤ ∑ w ∈ G.neighborFinset u, |x w| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ w ∈ G.neighborFinset u, |x u| := sum_le_sum fun w _ => hu w (mem_univ w)
      _ = G.degree u * |x u| := by simp
      _ ≤ G.maxDegree * |x u| := by
          gcongr
          exact_mod_cast G.degree_le_maxDegree u
  exact (le_abs_self lam).trans (le_of_mul_le_mul_right hbound hpos)

omit [Nonempty V] in
/-- **Wilf's theorem (1967).** A finite graph is `(⌊λ_max⌋ + 1)`-colourable, where `λ_max` is
the largest eigenvalue of its adjacency matrix. -/
theorem wilf : G.Colorable (⌊⨆ i, hA.eigenvalues i⌋₊ + 1) := by
  obtain ⟨f, hf⟩ := exists_coloring_of_low_degree G ⌊⨆ i, hA.eigenvalues i⌋₊
    (fun S hS => by
      obtain ⟨v, hv, hdeg⟩ := exists_low_degree G hA S hS
      exact ⟨v, hv, Nat.le_floor hdeg⟩) univ
  exact ⟨Coloring.mk f fun {u w} huw => hf u (mem_univ u) w (mem_univ w) huw⟩

/-- **Hoffman's bound (1970).** If a finite graph has at least one edge, every proper colouring
with `c` colours satisfies `1 - λ_max / λ_min ≤ c`. -/
theorem hoffman_chromatic (hE : G.edgeSet.Nonempty) {c : ℕ} (hc : G.Colorable c) :
    1 - (⨆ i, hA.eigenvalues i) / (⨅ i, hA.eigenvalues i) ≤ c := by
  obtain ⟨C⟩ := hc
  obtain ⟨x, hx, hxx⟩ := exists_unit_eigenvector_iSup hA
  set lam := ⨆ i, hA.eigenvalues i
  set mu := ⨅ i, hA.eigenvalues i
  have hmu : mu ≤ -1 := iInf_eigenvalues_le_neg_one G hA hE
  set z : Fin c → V → ℝ := fun j v => if C v = j then x v else 0
  have hzz : ∀ j, z j ⬝ᵥ z j = z j ⬝ᵥ x := fun j => by
    simp only [z, dotProduct]
    refine sum_congr rfl fun v _ => ?_
    split_ifs <;> simp
  have hz0 : ∀ j, 0 ≤ z j ⬝ᵥ x := fun j => by
    rw [← hzz]
    exact sum_nonneg fun v _ => mul_self_nonneg _
  have hclass : ∀ j, (lam - mu) * (z j ⬝ᵥ x) ≤ -mu := fun j => by
    have hind : z j ⬝ᵥ (G.adjMatrix ℝ *ᵥ z j) = 0 := by
      refine quadForm_eq_zero_of_indep G _ fun u v huv => ?_
      by_contra hne
      push Not at hne
      simp only [z, ne_eq, ite_eq_right_iff, not_forall] at hne
      exact C.valid huv (hne.1.1.trans hne.2.1.symm)
    have h := hoffman_key G hA x (z j) lam (z j ⬝ᵥ x) hx hind
    rw [hzz, hxx] at h
    rcases (hz0 j).lt_or_eq with hs | hs
    · nlinarith
    · rw [← hs]; linarith
  have hsum : ∑ j, z j ⬝ᵥ x = 1 := by
    rw [← hxx]
    simp only [z, dotProduct, ite_mul, zero_mul]
    rw [sum_comm]
    simp
  have htot : lam - mu ≤ -(c * mu) := by
    have := sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin c))) => hclass j
    rw [← mul_sum, hsum] at this
    simpa using this
  have hneg : mu < 0 := by linarith
  have h1 : 1 - (c : ℝ) ≤ lam / mu := by
    rw [le_div_iff_of_neg hneg]
    linarith
  linarith

/-- **Hoffman's ratio bound.** If a finite graph is `k`-regular with `k ≥ 1`, every independent
set has at most `n (−λ_min) / (k − λ_min)` vertices. -/
theorem hoffman_ratio {k : ℕ} (hk : 1 ≤ k) (hreg : G.IsRegularOfDegree k) {s : Finset V}
    (hs : G.IsIndepSet (s : Set V)) :
    (#s : ℝ) ≤ Fintype.card V * (-(⨅ i, hA.eigenvalues i)) / (k - ⨅ i, hA.eigenvalues i) := by
  set mu := ⨅ i, hA.eigenvalues i
  have hmu : mu ≤ 0 := iInf_eigenvalues_nonpos G hA
  set x : V → ℝ := fun _ => 1
  set z : V → ℝ := fun v => if v ∈ s then 1 else 0
  set n : ℝ := (Fintype.card V : ℝ)
  set a : ℝ := (#s : ℝ)
  have hn : 0 < n := by simp only [n]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
  have hx : G.adjMatrix ℝ *ᵥ x = (k : ℝ) • x := by
    ext v
    simp [x, hreg v]
  have hind : z ⬝ᵥ (G.adjMatrix ℝ *ᵥ z) = 0 := by
    refine quadForm_eq_zero_of_indep G _ fun u v huv => ?_
    by_contra hne
    push Not at hne
    simp only [z, ne_eq, ite_eq_right_iff, not_forall] at hne
    exact hs hne.1.1 hne.2.1 huv.ne huv
  have hzz : z ⬝ᵥ z = a := by simp [z, a, dotProduct]
  have hzx : z ⬝ᵥ x = a := by simp [z, x, a, dotProduct]
  have hxx : x ⬝ᵥ x = n := by simp [x, n, dotProduct]
  have h := hoffman_key G hA x z k (a / n) hx hind
  rw [hzz, hzx, hxx] at h
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : 0 < (k : ℝ) - mu := by linarith
  rw [le_div_iff₀ hden]
  have ht : a / n * n = a := div_mul_cancel₀ a hn.ne'
  set t := a / n
  have ha : 0 ≤ a := by positivity
  have h' : mu * (t * n) * (1 - t) ≤ -(k * t ^ 2 * n) := by
    have : a = t * n := ht.symm
    rw [this] at h
    nlinarith
  rcases ha.lt_or_eq with hapos | ha0
  · have htpos : 0 < t := by positivity
    have h2 : mu * (1 - t) ≤ -(k * t) := by
      have h3 : t * n * (mu * (1 - t)) ≤ t * n * (-(k * t)) := by nlinarith
      exact le_of_mul_le_mul_left h3 (by positivity)
    rw [← ht]
    nlinarith
  · rw [← ha0]
    nlinarith

end SpectralBounds
