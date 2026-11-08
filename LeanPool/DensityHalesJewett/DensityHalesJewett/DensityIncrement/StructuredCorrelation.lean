/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.DensityHalesJewett.DensityIncrement.CorrelatedFibers
public import LeanPool.DensityHalesJewett.DensityHalesJewett.Insensitive
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Structured correlation with insensitive intersections

Endpoint families turn many complete restricted-alphabet lines into a large intersection of
insensitive families. Its complement is partitioned into the pieces
`P_i = (C_i)ᶜ ∩ C_1 ∩ ⋯ ∩ C_(i-1)`, and one of them is an intersection of insensitive families
correlated with the ambient word family.
-/

@[expose] public section

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

variable {N : ℕ}

/-- `(k / (k + 1)) ^ m ≤ η` for every `m ≥ ⌈k / η⌉₊`, by Bernoulli's inequality
`(k / (k + 1)) ^ m ≤ k / (k + m)`. -/
lemma div_add_one_pow_le {k m : ℕ} (hk : 0 < k) {η : ℝ} (hη : 0 < η)
    (hm : ⌈(k : ℝ) / η⌉₊ ≤ m) : ((k : ℝ) / (k + 1)) ^ m ≤ η := by
  have hk : (0 : ℝ) < k := mod_cast hk
  rw [Nat.ceil_le, div_le_iff₀ hη] at hm
  rw [(by field_simp : (k : ℝ) / (k + 1) = (1 + 1 / (k : ℝ))⁻¹), inv_pow,
    inv_le_comm₀ (by positivity) hη]
  refine le_trans ?_ (one_add_mul_le_pow (by linarith [one_div_pos.2 hk]) m)
  rw [inv_le_iff_one_le_mul₀ hη]
  field_simp
  linarith [mul_pos hk hη]

/-- Replace every occurrence of the final alphabet letter by a fixed restricted-alphabet
letter. -/
def replaceLastLetter {k m : ℕ} (i : Fin k) (x : Fin m → Fin (k + 1)) :
    Fin m → Fin (k + 1) :=
  fun c ↦ if x c = Fin.last k then i.castSucc else x c

/-- The endpoint family associated with one restricted-alphabet letter. -/
def endpointFamily {k m n : ℕ}
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (i : Fin k) : Finset (Fin m → Fin (k + 1)) :=
  univ.filter fun x ↦ V (replaceLastLetter i x) ∈ A

/-- Parameter words which avoid the final alphabet letter. -/
def restrictedParameterWords (k m : ℕ) : Finset (Fin m → Fin (k + 1)) :=
  Fintype.piFinset fun _ ↦ {Fin.last k}ᶜ

lemma card_restrictedParameterWords (k m : ℕ) :
    (restrictedParameterWords k m).card = k ^ m := by
  simp [restrictedParameterWords, card_compl]

lemma dens_restrictedParameterWords (k m : ℕ) :
    ((restrictedParameterWords k m).dens : ℝ) = ((k : ℝ) / (k + 1)) ^ m := by
  simp [nnratCast_dens, card_restrictedParameterWords, div_pow]

/-- Each endpoint family is insensitive to interchanging its selected letter with the final
letter. -/
lemma endpointFamily_isInsensitive {k m n : ℕ}
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)) (i : Fin k) :
    IsInsensitive i.castSucc (Fin.last k) (endpointFamily A V i) := by
  intro x y hxy
  have hreplace : replaceLastLetter i x = replaceLastLetter i y := by
    funext c
    by_cases hxi : x c = i.castSucc <;> by_cases hyi : y c = i.castSucc <;>
      grind [replaceLastLetter, hxy (x c), hxy (y c)]
  simp only [endpointFamily, mem_filter, mem_univ, true_and]
  rw [hreplace]

/-- Encode a restricted-alphabet line by the word using the final letter on its wildcard
coordinates. -/
private def lineEndpoint {k m : ℕ} (l : Combinatorics.Line (Fin k) (Fin m)) :
    Fin m → Fin (k + 1) :=
  fun c ↦
    match l.idxFun c with
    | none => Fin.last k
    | some a => a.castSucc

/-- The endpoint word remembers every fixed letter and every wildcard coordinate of a line. -/
private lemma lineEndpoint_injective {k m : ℕ} :
    Function.Injective (lineEndpoint : Combinatorics.Line (Fin k) (Fin m) →
      (Fin m → Fin (k + 1))) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ hll
  congr
  funext c
  have hc := congrFun hll c
  cases hfc : f c <;> cases hgc : g c <;>
    simp_all [lineEndpoint, Fin.castSucc_ne_last, eq_comm (a := Fin.last k)]

private lemma replaceLastLetter_lineEndpoint {k m : ℕ} (i : Fin k)
    (l : Combinatorics.Line (Fin k) (Fin m)) :
    replaceLastLetter i (lineEndpoint l) = Fin.castSucc ∘ l i := by
  funext c
  cases hc : l.idxFun c <;>
    simp [lineEndpoint, replaceLastLetter, Combinatorics.Line.coe_apply, hc, Fin.castSucc_ne_last]

/-- Encoding lines by their endpoint words scales densities by the proportion of words using the
final letter. -/
private lemma dens_map_lineEndpoint {k m : ℕ} (hk : 0 < k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    (s : Finset (Combinatorics.Line (Fin k) (Fin m))) :
    ((s.map ⟨lineEndpoint, lineEndpoint_injective⟩).dens : ℝ) =
      s.dens * (1 - (restrictedParameterWords k m).dens) := by
  rw [nnratCast_dens, card_map, ← nnratCast_dens_mul_natCast_card s, Subspace.card_line m hk,
    Nat.cast_sub (Nat.pow_le_pow_left k.le_succ m), dens_restrictedParameterWords, div_pow]
  simp only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow, Nat.cast_succ]
  field_simp

/-- The endpoint words of the restricted-alphabet lines whose points `V` maps into `A` lie in
every endpoint family, so many such lines give a dense intersection of endpoint families. -/
lemma endpointFamily_intersection_dense {k m n : ℕ} (hk : 0 < k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))] {θ : ℝ}
    {A : Finset (Fin n → Fin (k + 1))}
    {V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)}
    (hrestricted : ((restrictedParameterWords k m).dens : ℝ) ≤ 1 / 2)
    (hlines : θ / 2 ≤
      ((univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
        ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ)) :
    θ / 4 ≤ ((IsInsensitive.intersection (endpointFamily A V)).dens : ℝ) := by
  classical
  set s := univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
    ∀ a, V (Fin.castSucc ∘ l a) ∈ A
  calc θ / 4 ≤ (s.dens : ℝ) * (1 - (restrictedParameterWords k m).dens) := by
        nlinarith [(by positivity : (0 : ℝ) ≤ s.dens)]
    _ = ((s.map ⟨lineEndpoint, lineEndpoint_injective⟩).dens : ℝ) :=
        (dens_map_lineEndpoint hk s).symm
    _ ≤ _ := mod_cast dens_le_dens <| map_subset_iff_subset_preimage.2 fun l hl ↦ by
        simpa [s, endpointFamily, replaceLastLetter_lineEndpoint] using hl

/-- In a line-free ambient family, a word lying both in its pullback and in every endpoint family
cannot use the final alphabet letter. -/
lemma pullback_inter_endpointFamily_subset_restricted {k m n : ℕ}
    {A : Finset (Fin n → Fin (k + 1))}
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (hfree : IsLineFree A) :
    pullback V A ∩ IsInsensitive.intersection (endpointFamily A V) ⊆
      restrictedParameterWords k m := by
  intro x hx
  obtain ⟨hxpull, hxinter⟩ := mem_inter.mp hx
  simp only [restrictedParameterWords, Fintype.mem_piFinset, mem_compl, mem_singleton]
  intro c hc
  let p : Combinatorics.Line (Fin (k + 1)) (Fin m) := {
    idxFun := fun i ↦ if x i = Fin.last k then none else some (x i)
    proper := ⟨c, ite_eq_left hc⟩
  }
  have hp_last : p (Fin.last k) = x := by
    funext i
    by_cases hi : x i = Fin.last k <;> simp [p, Combinatorics.Line.coe_apply, hi]
  have hp_cast (i : Fin k) : p i.castSucc = replaceLastLetter i x := by
    funext j
    by_cases hj : x j = Fin.last k <;> simp [p, replaceLastLetter, Combinatorics.Line.coe_apply, hj]
  obtain ⟨a, ha⟩ := hfree (Subspace.composeLine V p)
  apply ha
  rw [Subspace.composeLine_apply]
  obtain ⟨i, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last a
  · rw [hp_cast]
    simpa [endpointFamily] using IsInsensitive.mem_intersection.mp hxinter i
  · rw [hp_last]
    simpa [pullback, parameterPreimage] using hxpull

/-- Many complete restricted-alphabet lines yield a large insensitive intersection whose part
inside a line-free family is small. -/
lemma exists_endpoint_insensitive_intersection {k m n : ℕ} (hk : 2 ≤ k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))] {δ : ℝ} (hδ₁ : δ ≤ 1)
    (hm_large : ((k : ℝ) / (k + 1)) ^ m ≤ Parameters.η k N δ)
    {A : Finset (Fin n → Fin (k + 1))}
    {V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)}
    (hfree : IsLineFree A)
    (hlines : Parameters.θ k N δ / 2 ≤
      ((univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
        ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ)) :
    ∃ C : Fin k → Finset (Fin m → Fin (k + 1)),
      (∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) ∧
      Parameters.θ k N δ / 4 ≤ ((IsInsensitive.intersection C).dens : ℝ) ∧
      ((pullback V A ∩ IsInsensitive.intersection C).dens : ℝ) ≤
        Parameters.η k N δ := by
  rw [← dens_restrictedParameterWords] at hm_large
  refine ⟨endpointFamily A V, endpointFamily_isInsensitive A V, ?_, ?_⟩
  · refine endpointFamily_intersection_dense (by omega) ?_ hlines
    linarith [Parameters.η_le_δ_div_six k N δ]
  · exact le_trans (mod_cast dens_mono <|
      pullback_inter_endpointFamily_subset_restricted V hfree) hm_large

/-- Removing an intersection of density at least `θ / 4`, while losing at most `η` of a family
of density `δ - 2η`, gives the two complement estimates used below. -/
lemma density_complement_bounds {X : Type*} [Fintype X] [Nonempty X]
    [DecidableEq X] {A C : Finset X} {δ η θ : ℝ}
    (hδ₀ : 0 ≤ δ) (hη₀ : 0 ≤ η) (hA : δ - 2 * η ≤ (A.dens : ℝ))
    (hC : θ / 4 ≤ (C.dens : ℝ))
    (hAC : ((A ∩ C).dens : ℝ) ≤ η)
    (hgain : (δ + 6 * η) * (1 - θ / 4) ≤ δ - 3 * η) :
    (δ + 6 * η) * ((Cᶜ).dens : ℝ) ≤ ((A ∩ Cᶜ).dens : ℝ) ∧
      δ - 3 * η ≤ ((A ∩ Cᶜ).dens : ℝ) := by
  have hsplitA : ((A ∩ C).dens : ℝ) + ((A ∩ Cᶜ).dens : ℝ) = (A.dens : ℝ) := by
    norm_cast
    simpa [sdiff_eq_inter_compl] using dens_inter_add_dens_sdiff A C
  have hsplitC : ((Cᶜ).dens : ℝ) + (C.dens : ℝ) = 1 := by
    norm_cast
    simpa [← compl_eq_univ_sdiff] using dens_sdiff_add_dens_eq_dens C.subset_univ
  exact ⟨(mul_le_mul_of_nonneg_left (by linarith) (by linarith)).trans
    (hgain.trans (by linarith)), by linarith⟩

/-- The piece `P_i = (C_i)ᶜ ∩ C_1 ∩ ⋯ ∩ C_(i-1)` of the partition of the complement of
`C_1 ∩ ⋯ ∩ C_k`. -/
def complPiece {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) (i : Fin k) : Finset X :=
  univ.filter fun x ↦ x ∉ C i ∧ ∀ j < i, x ∈ C j

@[simp]
lemma mem_complPiece {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    {C : Fin k → Finset X} {i : Fin k} {x : X} :
    x ∈ complPiece C i ↔ x ∉ C i ∧ ∀ j < i, x ∈ C j := by
  simp [complPiece]

/-- The family `D` with `D_j = C_j` for `j < i`, `D_i = (C_i)ᶜ` and `D_j = univ` for `j > i`, whose
intersection is the piece `P_i`. -/
def complPieceFamily {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) (i : Fin k) : Fin k → Finset X :=
  fun j ↦ if j < i then C j else if j = i then (C j)ᶜ else univ

/-- Every member of the family has the required sensitivity pair. -/
lemma complPieceFamily_isInsensitive {k : ℕ} {ι : Type*}
    [Fintype (ι → Fin (k + 1))] [DecidableEq (ι → Fin (k + 1))]
    {C : Fin k → Finset (ι → Fin (k + 1))}
    (hC : ∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) (i j : Fin k) :
    IsInsensitive j.castSucc (Fin.last k) (complPieceFamily C i j) := by
  unfold complPieceFamily
  split_ifs
  · exact hC j
  · exact (hC j).compl
  · simp [IsInsensitive]

/-- The intersection of the family is the piece `P_i`. -/
lemma complPieceFamily_intersection {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) (i : Fin k) :
    IsInsensitive.intersection (complPieceFamily C i) = complPiece C i := by
  ext x
  simp only [IsInsensitive.mem_intersection, mem_complPiece, complPieceFamily]
  refine ⟨fun h ↦ ⟨by simpa using h i, fun j hj ↦ by simpa [hj] using h j⟩, ?_⟩
  rintro ⟨hi, hlt⟩ j
  obtain hj | rfl | hj := lt_trichotomy j i
  · simpa [hj] using hlt j hj
  · simpa
  · simp [hj.not_gt, hj.ne']

/-- The pieces cover the complement of the intersection. -/
lemma complPiece_biUnion {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) :
    univ.biUnion (complPiece C) = (IsInsensitive.intersection C)ᶜ := by
  ext x
  simp only [mem_biUnion, mem_univ, true_and, mem_complPiece, mem_compl,
    IsInsensitive.mem_intersection, not_forall]
  refine ⟨fun ⟨i, hi, _⟩ ↦ ⟨i, hi⟩, ?_⟩
  rintro ⟨j, hj⟩
  obtain ⟨i, hi, hmin⟩ := wellFounded_lt.has_min {i | x ∉ C i} ⟨j, hj⟩
  exact ⟨i, hi, fun j hji ↦ not_not.1 fun hj ↦ hmin j hj hji⟩

/-- Distinct pieces are disjoint. -/
lemma complPiece_pairwiseDisjoint {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) :
    ((univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint (complPiece C) := by
  intro i _ j _ hij
  rw [Function.onFun, disjoint_left]
  intro x hxi hxj
  rw [mem_complPiece] at hxi hxj
  obtain hij | hji := hij.lt_or_gt
  · exact hxi.1 (hxj.2 i hij)
  · exact hxj.1 (hxi.2 j hji)

/-- The pieces split the part of `A` outside the intersection. -/
lemma sum_dens_inter_complPiece {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (A : Finset X) (C : Fin k → Finset X) :
    ∑ i, ((A ∩ complPiece C i).dens : ℝ) =
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ) := by
  rw [← complPiece_biUnion, inter_biUnion,
    dens_biUnion ((complPiece_pairwiseDisjoint C).mono fun _ ↦ inter_subset_right),
    NNRat.cast_sum]

/-- The pieces partition the complement of the intersection. -/
lemma sum_dens_complPiece {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) :
    ∑ i, ((complPiece C i).dens : ℝ) = ((IsInsensitive.intersection C)ᶜ.dens : ℝ) := by
  simpa using sum_dens_inter_complPiece univ C

/-- If `a ≤ c` pointwise and `ε * ∑ i, c i + card ι * γ ≤ ∑ i, a i`, then some `i` has
`γ ≤ c i` and `ε * c i ≤ a i`. -/
lemma exists_le_and_mul_le_of_sum_le {ι : Type*} [Fintype ι] [Nonempty ι] {a c : ι → ℝ}
    {ε γ : ℝ} (hε : 0 ≤ ε) (hγ : 0 ≤ γ) (hc : ∀ i, 0 ≤ c i) (hac : ∀ i, a i ≤ c i)
    (h : ε * ∑ i, c i + Fintype.card ι * γ ≤ ∑ i, a i) :
    ∃ i, γ ≤ c i ∧ ε * c i ≤ a i := by
  by_contra! hlt
  have hlt' (i : ι) : a i < ε * c i + γ := by
    by_cases hi : γ ≤ c i
    · linarith [hlt i hi]
    · nlinarith [hac i, mul_nonneg hε (hc i)]
  have hsum := sum_lt_sum_of_nonempty univ_nonempty fun i _ ↦ hlt' i
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul] at hsum
  linarith

/-- Two global density estimates on the complement of `intersection C` make one piece
both large and relatively dense in `A`. -/
lemma exists_dense_complPiece {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {X : Type*} [Fintype X] [DecidableEq X]
    {A : Finset X} {C : Fin k → Finset X}
    (hweighted : (δ + 6 * Parameters.η k N δ) *
        ((IsInsensitive.intersection C)ᶜ.dens : ℝ) ≤
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ))
    (hlarge : δ - 3 * Parameters.η k N δ ≤
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ)) :
    ∃ i : Fin k,
      Parameters.γ k N δ ≤ ((complPiece C i).dens : ℝ) ∧
      (δ + Parameters.γ k N δ) * ((complPiece C i).dens : ℝ) ≤
        ((A ∩ complPiece C i).dens : ℝ) := by
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hc : ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ) ≤
      ((IsInsensitive.intersection C)ᶜ.dens : ℝ) := mod_cast dens_le_dens inter_subset_right
  have hγ := Parameters.γ_pos hk N hδ₀
  refine exists_le_and_mul_le_of_sum_le (by positivity) hγ.le (fun _ ↦ by positivity)
    (fun _ ↦ mod_cast dens_le_dens inter_subset_right) ?_
  rw [sum_dens_inter_complPiece, sum_dens_complPiece, Fintype.card_fin]
  linarith [Parameters.add_γ_mul_add_mul_γ_le (by omega : 0 < k) N hδ₀ hδ₁
    (c := ((IsInsensitive.intersection C)ᶜ.dens : ℝ))
    (by linarith [Parameters.η_le_δ_div_six k N δ])]

/-- Correlation with a positive-density intersection of insensitive families. -/
lemma exists_structured_correlation {k : ℕ} (hk : 2 ≤ k)
    {m n : ℕ} (hm : 1 ≤ m)
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    {δ : ℝ} (hN : IsDHJDimension k (δ / 4) (N + 1)) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_large : ((k : ℝ) / (k + 1)) ^ m ≤ Parameters.η k N δ)
    (hn : manyLinesBound k N m δ ≤ n)
    {A : Finset (Fin n → Fin (k + 1))} (hA : δ ≤ (A.dens : ℝ))
    (hfree : IsLineFree A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      ∃ D : Fin k → Finset (Fin m → Fin (k + 1)),
        (∀ i, IsInsensitive i.castSucc (Fin.last k) (D i)) ∧
        Parameters.γ k N δ ≤ ((IsInsensitive.intersection D).dens : ℝ) ∧
        (δ + Parameters.γ k N δ) * ((IsInsensitive.intersection D).dens : ℝ) ≤
          ((pullback V A ∩ IsInsensitive.intersection D).dens : ℝ) := by
  classical
  let : Fintype (Combinatorics.Line (Fin k) (Fin m)) :=
    Fintype.ofInjective (fun l ↦ l.idxFun) fun _ _ h ↦ Combinatorics.Line.ext h
  obtain ⟨V, hV⟩ | ⟨V, hV, hlines⟩ := exists_subspace_many_lines hk hm hN hδ₀ hδ₁ hn hA
  · refine ⟨V, fun _ ↦ univ, fun _ ↦ by simp [IsInsensitive], ?_⟩
    have hη := Parameters.η_le_δ_div_six k N δ
    have hγ := Parameters.γ_le_η_sq_div_two k N δ
    rw [(by ext; simp : IsInsensitive.intersection
      (fun _ : Fin k ↦ (univ : Finset (Fin m → Fin (k + 1)))) = univ), dens_univ, inter_univ,
      NNRat.cast_one, mul_one]
    rw [← dens_pullback] at hV
    exact ⟨by nlinarith [Parameters.η_pos k N hδ₀], by linarith⟩
  obtain ⟨C, hC, hCdense, hAC⟩ :=
    exists_endpoint_insensitive_intersection hk hδ₁ hm_large hfree hlines
  obtain ⟨hweighted, hlarge⟩ := density_complement_bounds (A := pullback V A) hδ₀.le
    (Parameters.η_pos k N hδ₀).le (by rwa [dens_pullback]) hCdense hAC
    (Parameters.mul_one_sub_θ_div_four_le k N hδ₀)
  obtain ⟨i, hi⟩ := exists_dense_complPiece hk hδ₀ hδ₁ hweighted hlarge
  refine ⟨V, complPieceFamily C i, complPieceFamily_isInsensitive hC i, ?_⟩
  rwa [complPieceFamily_intersection]

end DensityHalesJewett
