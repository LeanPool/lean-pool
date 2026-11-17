/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# Hashing triples into a set without arithmetic progressions

Let `A`, `B` and `C` be sets of vectors in `Fin n → ℕ`, and let `V` be the set of the triples
`(a, b, c)` in `A ×ˢ B ×ˢ C` with `a r + b r + c r = p - 1` for every `r`. A hash `(h, α, β)` with
values in `ZMod P` sends `a` to `β + h ⬝ᵥ a` and `c` to `α + h ⬝ᵥ c`. The triples whose two hashes
agree and lie in a set `S` without three-term arithmetic progressions, and which share no vector
with another such triple, form a multicolored sum-free family. Averaging over all hashes gives one
where this family is large. This is the construction of Section 4 of Kleinberg, Sawin and Speyer.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.vecSumTriples p A B C`: the triples `(a, b, c)` of
  `A ×ˢ B ×ˢ C` with `a r + b r + c r = p - 1` for every `r`.
* `ArithmeticTriangleRemovalInVectorSpaces.Shares v v'`: the triples `v` and `v'` agree in some
  coordinate.
* `ArithmeticTriangleRemovalInVectorSpaces.hashedTriples V S θ`: the triples of `V` whose hashes
  under `θ` agree and lie in `S`.
* `ArithmeticTriangleRemovalInVectorSpaces.isolatedTriples V S θ`: the hashed triples sharing no
  vector with another hashed triple.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.isMulticoloredSumFree_isolatedTriples`: the isolated
  triples form a multicolored sum-free family (Lemma 4.3 of Kleinberg, Sawin and Speyer).
* `ArithmeticTriangleRemovalInVectorSpaces.exists_isMulticoloredSumFree_of_hash`: some hash leaves
  at least `#V * #S * (P - F) / P ^ 3` isolated triples, where `F` bounds the number of triples
  sharing a vector with a given one (Lemma 4.6 of Kleinberg, Sawin and Speyer).
-/

public section

open Finset Matrix

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {n p P F : ℕ}

/-- The triples `(a, b, c)` of `A ×ˢ B ×ˢ C` with `a r + b r + c r = p - 1` for every `r`. -/
def vecSumTriples (p : ℕ) (A B C : Finset (Fin n → ℕ)) :
    Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)) :=
  (A ×ˢ B ×ˢ C).filter fun (a, b, c) ↦ ∀ r, a r + b r + c r = p - 1

/-- Two triples share a vector if they agree in some coordinate. -/
def Shares :
    (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ) → (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ) → Prop
  | (a, b, c), (a', b', c') => a = a' ∨ b = b' ∨ c = c'

instance : DecidableRel (Shares (n := n)) :=
  fun (a, b, c) (a', b', c') ↦ inferInstanceAs (Decidable (a = a' ∨ b = b' ∨ c = c'))

/-- The triples `(a, b, c)` of `V` whose hashes `β + h ⬝ᵥ a` and `α + h ⬝ᵥ c` under `(h, α, β)`
agree and lie in `S`. -/
private def hashedTriples (V : Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)))
    (S : Finset (ZMod P)) :
    (Fin n → ZMod P) × ZMod P × ZMod P → Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ))
  | (h, α, β) => V.filter fun (a, _, c) ↦ β + h ⬝ᵥ (fun r ↦ (a r : ZMod P)) ∈ S ∧
      α + h ⬝ᵥ (fun r ↦ (c r : ZMod P)) = β + h ⬝ᵥ (fun r ↦ (a r : ZMod P))

/-- The hashed triples that share no vector with another hashed triple. -/
private def isolatedTriples (V : Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)))
    (S : Finset (ZMod P)) (θ : (Fin n → ZMod P) × ZMod P × ZMod P) :
    Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)) :=
  {v ∈ hashedTriples V S θ | ∀ v' ∈ hashedTriples V S θ, Shares v v' → v' = v}

/-- The pairs of distinct triples of `V` sharing a vector. -/
private def sharingPairs (V : Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ))) :
    Finset (((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)) ×
      ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ))) :=
  (V ×ˢ V).filter fun (v, v') ↦ v ≠ v' ∧ Shares v v'

variable {A B C : Finset (Fin n → ℕ)} {V : Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ))}
  {S : Finset (ZMod P)} {θ : (Fin n → ZMod P) × ZMod P × ZMod P}
  {v v' : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)} {a b c a' b' c' : Fin n → ℕ}

@[simp]
lemma mk_mem_vecSumTriples :
    (a, b, c) ∈ vecSumTriples p A B C ↔ a ∈ A ∧ b ∈ B ∧ c ∈ C ∧ ∀ r, a r + b r + c r = p - 1 := by
  simp [vecSumTriples, and_assoc]

lemma card_vecSumTriples_le : #(vecSumTriples p A B C) ≤ #A * #B * #C := by
  grw [vecSumTriples, card_filter_le, card_product, card_product, mul_assoc]

@[simp]
lemma shares_mk : Shares (a, b, c) (a', b', c') ↔ a = a' ∨ b = b' ∨ c = c' :=
  Iff.rfl

@[simp]
private lemma mk_mem_hashedTriples {h : Fin n → ZMod P} {α β : ZMod P} :
    (a, b, c) ∈ hashedTriples V S (h, α, β) ↔ (a, b, c) ∈ V ∧
      β + h ⬝ᵥ (fun r ↦ (a r : ZMod P)) ∈ S ∧
      α + h ⬝ᵥ (fun r ↦ (c r : ZMod P)) = β + h ⬝ᵥ (fun r ↦ (a r : ZMod P)) :=
  mem_filter

private lemma hashedTriples_subset : hashedTriples V S θ ⊆ V := by
  obtain ⟨h, α, β⟩ := θ
  exact filter_subset _ _

private lemma mem_isolatedTriples :
    v ∈ isolatedTriples V S θ ↔
      v ∈ hashedTriples V S θ ∧ ∀ v' ∈ hashedTriples V S θ, Shares v v' → v' = v :=
  mem_filter

@[simp]
private lemma mk_mem_sharingPairs :
    (v, v') ∈ sharingPairs V ↔ (v ∈ V ∧ v' ∈ V) ∧ v ≠ v' ∧ Shares v v' := by
  simp [sharingPairs]

private lemma dotProduct_add_eq_of_add_eq (h : ∀ r, a r + c r = a' r + c' r) (u : Fin n → ZMod P) :
    u ⬝ᵥ (fun r ↦ (a r : ZMod P)) + u ⬝ᵥ (fun r ↦ (c r : ZMod P)) =
      u ⬝ᵥ (fun r ↦ (a' r : ZMod P)) + u ⬝ᵥ (fun r ↦ (c' r : ZMod P)) := by
  rw [← dotProduct_add, ← dotProduct_add]
  congr 1 with r
  simpa using congr_arg (Nat.cast : ℕ → ZMod P) (h r)

private lemma eq_of_natCast_eq_natCast (ha : ∀ r, a r < P) (ha' : ∀ r, a' r < P)
    (h : (fun r ↦ (a r : ZMod P)) = fun r ↦ (a' r : ZMod P)) : a = a' := by
  ext r
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 (congr_fun h r)
  rwa [Nat.mod_eq_of_lt (ha r), Nat.mod_eq_of_lt (ha' r)] at this

/-- If `∑ r, (a r + b r + c r) = n * (p - 1)`, then `a + b + c + 1` vanishes in `Fin n → ZMod p` if
and only if `a r + b r + c r = p - 1` for every `r`. -/
private lemma add_add_add_one_eq_zero_iff (hp : 0 < p)
    (hsum : ∑ r, (a r + b r + c r) = n * (p - 1)) :
    (fun r ↦ (a r : ZMod p)) + (fun r ↦ (b r : ZMod p)) + (fun r ↦ (c r : ZMod p) + 1) = 0 ↔
      ∀ r, a r + b r + c r = p - 1 := by
  have hcast (r : Fin n) :
      (a r : ZMod p) + b r + (c r + 1) = ((a r + b r + c r + 1 : ℕ) : ZMod p) := by
    push_cast
    ring
  simp only [funext_iff, Pi.add_apply, Pi.zero_apply, hcast, ZMod.natCast_eq_zero_iff]
  constructor
  · intro h
    have hge (r : Fin n) : p - 1 ≤ a r + b r + c r := by grind [Nat.le_of_dvd (by grind) (h r)]
    intro r
    exact ((sum_eq_sum_iff_of_le fun r _ ↦ hge r).1 (by simp [hsum]) r (mem_univ r)).symm
  · intro h r
    rw [h r, Nat.sub_add_cancel hp]

/-- If the hashed triples `(a₁, b₁, c₁)`, `(a₂, b₂, c₂)` and `(a₃, b₃, c₃)` satisfy
`a₁ + c₃ = a₂ + c₂`, then the hashes of `a₁` and `c₃` agree, since `S` has no three-term arithmetic
progressions. -/
private lemma mk_mem_hashedTriples_of_add_eq_add (hS : ThreeAPFree (S : Set (ZMod P)))
    {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : Fin n → ℕ} (h₁ : (a₁, b₁, c₁) ∈ hashedTriples V S θ)
    (h₂ : (a₂, b₂, c₂) ∈ hashedTriples V S θ) (h₃ : (a₃, b₃, c₃) ∈ hashedTriples V S θ)
    (hac : ∀ r, a₁ r + c₃ r = a₂ r + c₂ r) (hV : (a₁, b, c₃) ∈ V) :
    (a₁, b, c₃) ∈ hashedTriples V S θ := by
  obtain ⟨h, α, β⟩ := θ
  simp only [mk_mem_hashedTriples] at h₁ h₂ h₃ ⊢
  obtain ⟨-, hS₁, -⟩ := h₁
  obtain ⟨-, hS₂, hC₂⟩ := h₂
  obtain ⟨-, hS₃, hC₃⟩ := h₃
  have hrel := dotProduct_add_eq_of_add_eq hac h
  have hA : β + h ⬝ᵥ (fun r ↦ (a₁ r : ZMod P)) = β + h ⬝ᵥ (fun r ↦ (a₂ r : ZMod P)) :=
    hS hS₁ hS₂ hS₃ (by linear_combination hrel + hC₂ - hC₃)
  exact ⟨hV, hS₁, by linear_combination hrel + hC₂ - 2 * hA⟩

/-- **Lemma 4.3 of Kleinberg, Sawin and Speyer.** The isolated triples form a multicolored sum-free
family in `Fin n → ZMod p`, after shifting the third vectors by one. -/
private lemma isMulticoloredSumFree_isolatedTriples (hp : 0 < p)
    (hsum : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, ∑ r, (a r + b r + c r) = n * (p - 1))
    (hS : ThreeAPFree (S : Set (ZMod P))) (θ : (Fin n → ZMod P) × ZMod P × ZMod P) :
    IsMulticoloredSumFree (ι := isolatedTriples (vecSumTriples p A B C) S θ)
      (fun ⟨(a, _, _), _⟩ r ↦ (a r : ZMod p)) (fun ⟨(_, b, _), _⟩ r ↦ (b r : ZMod p))
      (fun ⟨(_, _, c), _⟩ r ↦ (c r : ZMod p) + 1) := by
  rintro ⟨⟨a₁, b₁, c₁⟩, hi⟩ ⟨⟨a₂, b₂, c₂⟩, hj⟩ ⟨⟨a₃, b₃, c₃⟩, hk⟩
  obtain ⟨hi, hiiso⟩ := mem_isolatedTriples.1 hi
  obtain ⟨hj, hjiso⟩ := mem_isolatedTriples.1 hj
  obtain ⟨hk, hkiso⟩ := mem_isolatedTriples.1 hk
  obtain ⟨ha₁, -, -, hi₀⟩ := mk_mem_vecSumTriples.1 (hashedTriples_subset hi)
  obtain ⟨-, hb₂, -, hj₀⟩ := mk_mem_vecSumTriples.1 (hashedTriples_subset hj)
  obtain ⟨-, -, hc₃, -⟩ := mk_mem_vecSumTriples.1 (hashedTriples_subset hk)
  simp only [Subtype.mk.injEq, Prod.mk.injEq]
  rw [add_add_add_one_eq_zero_iff hp (hsum _ ha₁ _ hb₂ _ hc₃)]
  constructor
  · intro h₀
    have hmem := mk_mem_hashedTriples_of_add_eq_add hS hi hj hk (by grind)
      (mk_mem_vecSumTriples.2 ⟨ha₁, hb₂, hc₃, h₀⟩)
    grind [hiiso _ hmem, hjiso _ hmem, hkiso _ hmem, shares_mk]
  · rintro ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
    exact hi₀

/-- There are `#H * #S` hashes `(h, α, β)` with `h ∈ H` under which `a` and `c` have the same hash
in `S`. -/
private lemma card_filter_hash [NeZero P] (a c : Fin n → ZMod P) (H : Finset (Fin n → ZMod P)) :
    #(univ.filter fun ((h, α, β) : (Fin n → ZMod P) × ZMod P × ZMod P) ↦
      h ∈ H ∧ β + h ⬝ᵥ a ∈ S ∧ α + h ⬝ᵥ c = β + h ⬝ᵥ a) = #H * #S := by
  rw [← card_product]
  refine card_nbij' (fun (h, _, β) ↦ (h, β + h ⬝ᵥ a))
    (fun (h, s) ↦ (h, s - h ⬝ᵥ c, s - h ⬝ᵥ a)) ?_ ?_ ?_ ?_
  · rintro ⟨h, α, β⟩
    simp +contextual
  · rintro ⟨h, s⟩
    simp
  · rintro ⟨h, α, β⟩
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, add_sub_cancel_right,
      Prod.mk.injEq, and_true, and_imp]
    grind
  · rintro ⟨h, s⟩
    simp

/-- A nonzero vector `u` is orthogonal to `P ^ n / P` vectors. -/
private lemma card_filter_dotProduct_eq_zero_mul [Fact P.Prime] {u : Fin n → ZMod P} (hu : u ≠ 0) :
    #{h : Fin n → ZMod P | h ⬝ᵥ u = 0} * P = P ^ n := by
  obtain ⟨r, hr⟩ := Function.ne_iff.1 hu
  let f : (Fin n → ZMod P) →+ ZMod P := AddMonoidHom.mk' (· ⬝ᵥ u) fun a b ↦ add_dotProduct a b u
  have hf : Function.Surjective f := by
    intro z
    refine ⟨Pi.single r (z / u r), ?_⟩
    simp [f, single_dotProduct, div_mul_cancel₀ z hr]
  have := AddSubgroup.card_ker_mul_card_of_surjective (f := f) hf
  rw [Nat.card_eq_fintype_card, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_pi] at this
  simpa [Fintype.card_subtype, f] using this

/-- A triple of `V` is hashed by `P ^ n * #S` hashes. -/
private lemma card_filter_mem_hashedTriples [NeZero P] (hv : v ∈ V) :
    #{θ | v ∈ hashedTriples V S θ} = P ^ n * #S := by
  obtain ⟨a, b, c⟩ := v
  convert card_filter_hash (S := S) (fun r ↦ (a r : ZMod P)) (fun r ↦ (c r : ZMod P)) univ
    using 2
  · ext ⟨h, α, β⟩
    simp [hv]
  · simp

/-- A triple of `V` is hashed by `P ^ n * #S / P` hashes `(h, α, β)` with `h ⬝ᵥ u = 0`, for a
nonzero `u`. -/
private lemma card_filter_mem_hashedTriples_dotProduct_eq_zero_mul [Fact P.Prime]
    {u : Fin n → ZMod P} (hu : u ≠ 0) (hv : v ∈ V) :
    #(univ.filter fun ((h, α, β) : (Fin n → ZMod P) × ZMod P × ZMod P) ↦
      v ∈ hashedTriples V S (h, α, β) ∧ h ⬝ᵥ u = 0) * P = P ^ n * #S := by
  obtain ⟨a, b, c⟩ := v
  rw [← card_filter_dotProduct_eq_zero_mul hu, mul_right_comm,
    ← card_filter_hash (S := S) (fun r ↦ (a r : ZMod P)) (fun r ↦ (c r : ZMod P))]
  congr 2
  ext ⟨h, α, β⟩
  simp only [mem_filter, mem_univ, true_and, mk_mem_hashedTriples]
  tauto

/-- Two distinct triples of `vecSumTriples p A B C` with entries less than `P` differ, after
casting to `ZMod P`, in their first or in their third vector. -/
private lemma natCast_ne_or_natCast_ne (hpP : p < P) (hv : (a, b, c) ∈ vecSumTriples p A B C)
    (hv' : (a', b', c') ∈ vecSumTriples p A B C) (hne : (a, b, c) ≠ (a', b', c')) :
    (fun r ↦ (a r : ZMod P)) ≠ (fun r ↦ (a' r : ZMod P)) ∨
      (fun r ↦ (c r : ZMod P)) ≠ (fun r ↦ (c' r : ZMod P)) := by
  obtain ⟨-, -, -, hv⟩ := mk_mem_vecSumTriples.1 hv
  obtain ⟨-, -, -, hv'⟩ := mk_mem_vecSumTriples.1 hv'
  by_contra! h
  obtain ⟨ha, hc⟩ := h
  obtain rfl := eq_of_natCast_eq_natCast (fun r ↦ by grind [hv r]) (fun r ↦ by grind [hv' r]) ha
  obtain rfl := eq_of_natCast_eq_natCast (fun r ↦ by grind [hv r]) (fun r ↦ by grind [hv' r]) hc
  apply hne
  ext r <;> grind [hv r, hv' r]

/-- If a hash `(h, α, β)` hashes two triples of `vecSumTriples p A B C` that share a vector, and
`2 ≠ 0` in `ZMod P`, then the hashes `h ⬝ᵥ a` of their first vectors agree, and so do those of their
third vectors. -/
private lemma dotProduct_eq_and_dotProduct_eq_of_shares [Fact P.Prime] (h2 : (2 : ZMod P) ≠ 0)
    {h : Fin n → ZMod P} {α β : ZMod P}
    (hv : (a, b, c) ∈ hashedTriples (vecSumTriples p A B C) S (h, α, β))
    (hv' : (a', b', c') ∈ hashedTriples (vecSumTriples p A B C) S (h, α, β))
    (hsh : Shares (a, b, c) (a', b', c')) :
    h ⬝ᵥ (fun r ↦ (a r : ZMod P)) = h ⬝ᵥ (fun r ↦ (a' r : ZMod P)) ∧
      h ⬝ᵥ (fun r ↦ (c r : ZMod P)) = h ⬝ᵥ (fun r ↦ (c' r : ZMod P)) := by
  simp only [mk_mem_hashedTriples, mk_mem_vecSumTriples] at hv hv'
  obtain ⟨⟨-, -, -, hv⟩, -, hC⟩ := hv
  obtain ⟨⟨-, -, -, hv'⟩, -, hC'⟩ := hv'
  rcases hsh with rfl | rfl | rfl
  · exact ⟨rfl, by linear_combination hC - hC'⟩
  · have hrel := dotProduct_add_eq_of_add_eq (fun r ↦ by grind [hv r, hv' r] :
      ∀ r, a r + c r = a' r + c' r) h
    have ha : h ⬝ᵥ (fun r ↦ (a r : ZMod P)) = h ⬝ᵥ (fun r ↦ (a' r : ZMod P)) :=
      mul_left_cancel₀ h2 (by linear_combination hrel - hC + hC')
    exact ⟨ha, by linear_combination hrel - ha⟩
  · exact ⟨by linear_combination hC' - hC, rfl⟩

/-- For two distinct triples of `vecSumTriples p A B C` sharing a vector, there is a nonzero `u`
with `h ⬝ᵥ u = 0` for every hash `(h, α, β)` that hashes both. -/
private lemma exists_ne_zero_dotProduct_eq_zero [Fact P.Prime] (hp : 2 ≤ p) (hpP : p < P)
    (hv : v ∈ vecSumTriples p A B C) (hv' : v' ∈ vecSumTriples p A B C) (hne : v ≠ v')
    (hsh : Shares v v') :
    ∃ u : Fin n → ZMod P, u ≠ 0 ∧ ∀ (h : Fin n → ZMod P) (α β : ZMod P),
      v ∈ hashedTriples (vecSumTriples p A B C) S (h, α, β) →
      v' ∈ hashedTriples (vecSumTriples p A B C) S (h, α, β) → h ⬝ᵥ u = 0 := by
  obtain ⟨a, b, c⟩ := v
  obtain ⟨a', b', c'⟩ := v'
  have h2 : (2 : ZMod P) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 P).not.2
      (Nat.not_dvd_of_pos_of_lt two_pos (by grind))
  rcases natCast_ne_or_natCast_ne hpP hv hv' hne with ha | hc
  · refine ⟨_, sub_ne_zero.2 ha, ?_⟩
    intro h α β h₁ h₂
    rw [dotProduct_sub, sub_eq_zero]
    exact (dotProduct_eq_and_dotProduct_eq_of_shares h2 h₁ h₂ hsh).1
  · refine ⟨_, sub_ne_zero.2 hc, ?_⟩
    intro h α β h₁ h₂
    rw [dotProduct_sub, sub_eq_zero]
    exact (dotProduct_eq_and_dotProduct_eq_of_shares h2 h₁ h₂ hsh).2

/-- Two distinct triples of `vecSumTriples p A B C` sharing a vector are both hashed by at most
`P ^ n * #S / P` hashes. -/
private lemma card_filter_mem_hashedTriples_mul_le [Fact P.Prime] (hp : 2 ≤ p) (hpP : p < P)
    (hv : v ∈ vecSumTriples p A B C) (hv' : v' ∈ vecSumTriples p A B C) (hne : v ≠ v')
    (hsh : Shares v v') :
    #{θ | v ∈ hashedTriples (vecSumTriples p A B C) S θ ∧
      v' ∈ hashedTriples (vecSumTriples p A B C) S θ} * P ≤ P ^ n * #S := by
  obtain ⟨u, hu, hθ⟩ := exists_ne_zero_dotProduct_eq_zero (S := S) hp hpP hv hv' hne hsh
  rw [← card_filter_mem_hashedTriples_dotProduct_eq_zero_mul hu hv]
  apply Nat.mul_le_mul_right
  apply card_le_card
  rintro ⟨h, α, β⟩
  simp only [mem_filter, mem_univ, true_and]
  rintro ⟨h₁, h₂⟩
  exact ⟨h₁, hθ h α β h₁ h₂⟩

private lemma sum_card_hashedTriples [NeZero P] :
    ∑ θ, #(hashedTriples V S θ) = #V * (P ^ n * #S) := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := univ) (t := V)
    (fun θ v ↦ v ∈ hashedTriples V S θ)
  simp only [bipartiteAbove, bipartiteBelow, filter_mem_eq_inter,
    inter_eq_right.2 hashedTriples_subset] at h
  rw [h, sum_const_nat]
  intro v hv
  exact card_filter_mem_hashedTriples hv

private lemma card_sharingPairs_le (hF : ∀ v ∈ V, #{v' ∈ V | Shares v v'} ≤ F) :
    #(sharingPairs V) ≤ #V * F := by
  rw [mul_comm]
  refine card_le_mul_card_image_of_maps_to (f := Prod.fst) ?_ F ?_
  · rintro ⟨v, v'⟩
    simp +contextual
  intro v hv
  grw [← hF v hv]
  apply card_le_card_of_injOn Prod.snd
  · rintro ⟨_, v'⟩
    simp only [coe_filter, Set.mem_ofPred_eq, mk_mem_sharingPairs]
    grind
  · rintro ⟨_, _⟩ h₁ ⟨_, _⟩ h₂
    simp only [coe_filter, Set.mem_ofPred_eq] at h₁ h₂
    grind

private lemma sharingPairs_eq_filter {W : Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ))}
    (hW : W ⊆ V) : sharingPairs W = (sharingPairs V).filter fun (v, v') ↦ v ∈ W ∧ v' ∈ W := by
  ext ⟨v, v'⟩
  simp only [mk_mem_sharingPairs, mem_filter]
  grind

/-- Summed over all hashes, the pairs of distinct hashed triples sharing a vector number at most
`#V * F * P ^ n * #S / P`. -/
private lemma sum_card_sharingPairs_hashedTriples_mul_le [Fact P.Prime] (hp : 2 ≤ p) (hpP : p < P)
    (hF : ∀ v ∈ vecSumTriples p A B C, #{v' ∈ vecSumTriples p A B C | Shares v v'} ≤ F) :
    (∑ θ, #(sharingPairs (hashedTriples (vecSumTriples p A B C) S θ))) * P ≤
      #(vecSumTriples p A B C) * F * (P ^ n * #S) := by
  simp only [sharingPairs_eq_filter hashedTriples_subset, card_filter]
  rw [sum_comm, sum_mul]
  grw [sum_le_sum (g := fun _ ↦ P ^ n * #S), sum_const, smul_eq_mul, card_sharingPairs_le hF]
  rintro ⟨v, v'⟩ hq
  obtain ⟨⟨hv, hv'⟩, hne, hsh⟩ := mk_mem_sharingPairs.1 hq
  rw [← card_filter]
  exact card_filter_mem_hashedTriples_mul_le hp hpP hv hv' hne hsh

/-- A hashed triple is isolated unless it is the first member of a pair of hashed triples sharing
a vector. -/
private lemma card_hashedTriples_le (θ : (Fin n → ZMod P) × ZMod P × ZMod P) :
    #(hashedTriples V S θ) ≤
      #(isolatedTriples V S θ) + #(sharingPairs (hashedTriples V S θ)) := by
  grw [← card_image_le (s := sharingPairs (hashedTriples V S θ)) (f := Prod.fst), ← card_union_le]
  apply card_le_card
  intro v hv
  by_cases hiso : v ∈ isolatedTriples V S θ
  · exact mem_union_left _ hiso
  simp only [mem_isolatedTriples, hv, true_and, not_forall] at hiso
  obtain ⟨v', hv', hsh, hne⟩ := hiso
  exact mem_union_right _ (mem_image.2 ⟨(v, v'), by simp [hv, hv', Ne.symm hne, hsh], rfl⟩)

/-- Summed over all hashes, the isolated triples number at least
`#V * P ^ n * #S * (P - F) / P`. -/
private lemma mul_le_mul_sum_card_isolatedTriples_add [Fact P.Prime] (hp : 2 ≤ p) (hpP : p < P)
    (hF : ∀ v ∈ vecSumTriples p A B C, #{v' ∈ vecSumTriples p A B C | Shares v v'} ≤ F) :
    #(vecSumTriples p A B C) * (P ^ n * #S) * P ≤
      P * ∑ θ, #(isolatedTriples (vecSumTriples p A B C) S θ) +
        #(vecSumTriples p A B C) * F * (P ^ n * #S) := by
  have h : ∑ θ, #(hashedTriples (vecSumTriples p A B C) S θ) ≤
      ∑ θ, (#(isolatedTriples (vecSumTriples p A B C) S θ) +
        #(sharingPairs (hashedTriples (vecSumTriples p A B C) S θ))) := by
    apply sum_le_sum
    intro θ _
    exact card_hashedTriples_le θ
  rw [sum_card_hashedTriples, sum_add_distrib] at h
  nlinarith [sum_card_sharingPairs_hashedTriples_mul_le (S := S) hp hpP hF]

/-- **Lemma 4.6 of Kleinberg, Sawin and Speyer.** Some hash leaves at least
`#V * #S * (P - F) / P ^ 3` isolated triples, which form a multicolored sum-free family. -/
lemma exists_isMulticoloredSumFree_of_hash [Fact P.Prime] (hp : 2 ≤ p) (hpP : p < P)
    (hsum : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, ∑ r, (a r + b r + c r) = n * (p - 1))
    (hF : ∀ v ∈ vecSumTriples p A B C, #{v' ∈ vecSumTriples p A B C | Shares v v'} ≤ F)
    (hS : ThreeAPFree (S : Set (ZMod P))) :
    ∃ (m : ℕ) (x y z : Fin m → Fin n → ZMod p), IsMulticoloredSumFree x y z ∧
      #(vecSumTriples p A B C) * #S * (P - F : ℝ) ≤ m * P ^ 3 := by
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have h : (#(vecSumTriples p A B C) * (P ^ n * #S) * P : ℝ) ≤
      P * ∑ θ, (#(isolatedTriples (vecSumTriples p A B C) S θ) : ℝ) +
        #(vecSumTriples p A B C) * F * (P ^ n * #S) := by
    exact_mod_cast mul_le_mul_sum_card_isolatedTriples_add hp hpP hF
  have havg : ∑ _θ : (Fin n → ZMod P) × ZMod P × ZMod P,
      #(vecSumTriples p A B C) * #S * (P - F : ℝ) / P ^ 3 ≤
        ∑ θ, (#(isolatedTriples (vecSumTriples p A B C) S θ) : ℝ) := by
    simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_pi, ZMod.card, prod_const,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ P ^ 2)]
  obtain ⟨θ, -, hθ⟩ := exists_le_of_sum_le univ_nonempty havg
  rw [div_le_iff₀ (by positivity)] at hθ
  exact ⟨_, _, _, _, (isMulticoloredSumFree_isolatedTriples (by grind) hsum hS θ).comp
    (isolatedTriples _ S θ).equivFin.symm.injective, hθ⟩

end ArithmeticTriangleRemovalInVectorSpaces
