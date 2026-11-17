/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.PoissonIterate.Basic

/-!
# Permutations of index positions and the bound (44) of BKL Lemma 3.3

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Lemma 3.3, p. 12–13, (44): the distance of a tensor
field from its symmetrization over the first `q` index positions is controlled by its distances
from the images under the adjacent transpositions of those positions.

## What is proved

For tensor fields `u : Field ν k` (families of `L²(ν)` classes indexed by `Fin k → Fin n`), with
`permField σ u = u (· ∘ σ)`, `S_q = symField q`, `normSq` the squared Hilbert–Schmidt norm and
`τ_ℓ = swap ℓ (ℓ + 1)` (written `Equiv.swap ℓ (finRotate k ℓ)`):

* the algebra of `permField`: `permField_one`, `permField_mul` (a left action,
  `permField (σ * τ) = permField σ ∘ permField τ`), additivity, homogeneity and `permField_sum`,
  and linearity of `symField` (`symField_add`, `symField_sub`, `symField_smul`);
* `normSq_permField`: `permField σ` preserves `normSq`;
* the Hilbert–Schmidt norm `√(normSq u)` is a norm (`sqrt_normSq_add_le`, `sqrt_normSq_smul`,
  `sqrt_normSq_sum_le`), being the norm of `u` in `PiLp 2` (`normSq_eq_norm_toLp_sq`);
* `sqrt_normSq_sub_permField_le_of_adjacent`: if `√(normSq (u - τ_ℓ u)) ≤ B` for every `ℓ` with
  `ℓ + 1 < q`, then `√(normSq (u - π u)) ≤ q² B` for every permutation `π` of the first `q`
  positions;
* `normSq_sub_permField_le`: `‖u - π u‖² ≤ q⁴ Σ_{ℓ+1<q} ‖u - τ_ℓ u‖²`, the first half of (44);
* `normSq_sub_symField_le`: **(44)**, `‖u - S_q u‖² ≤ q⁴ Σ_{ℓ+1<q} ‖u - τ_ℓ u‖²`.

## The argument

The displacement `d(π) = √(normSq (u - π u))` is subadditive, `d(σ τ) ≤ d(σ) + d(τ)`, since
`u - σ τ u = (u - σ u) + σ (u - τ u)` and `σ` is an isometry; and `d(σ⁻¹) = d(σ)`. A permutation
`σ` of the first `p + 1` positions is `ρ⁻¹ (ρ σ)`, where `ρ = τ_{p-1} ⋯ τ_a` carries `a = σ p` to
`p` with at most `p` adjacent transpositions, and `ρ σ` permutes the first `p` positions; by
induction `d(σ) ≤ p B + p² B ≤ (p + 1)² B`. This replaces the source's word decomposition with
`m ≤ q²` letters and Cauchy–Schwarz by the triangle inequality, with the same constant. Finally
`u - S_q u` is the average of `u - π u` over the group, so its norm is at most `q² B` with
`B² = Σ_{ℓ+1<q} ‖u - τ_ℓ u‖²`.

## What this is not

Only the combinatorial bound (44) is proved here; the rest of Lemma 3.3 (the commutation of `S_q`
with the gradient and the Poisson iterates) is not part of this module. The statement is about
an arbitrary family of `L²` classes and uses nothing of the measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open FunctionalInequalities.Analysis.Tensor

namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  {ν : ProbabilityMeasure V} {k : ℕ}

/-! ### The algebra of `permField` and `symField` -/

@[simp] theorem permField_apply (σ : Equiv.Perm (Fin k)) (u : Field ν k)
    (I : Fin k → Fin (Module.finrank ℝ V)) : permField σ u I = u (I ∘ σ) := rfl

/-- The identity permutation acts trivially. -/
@[simp] theorem permField_one (u : Field ν k) : permField 1 u = u := rfl

/-- `permField` is a left action: `permField (σ * τ) = permField σ ∘ permField τ`. -/
theorem permField_mul (σ τ : Equiv.Perm (Fin k)) (u : Field ν k) :
    permField (σ * τ) u = permField σ (permField τ u) := rfl

/-- `permField σ` is additive. -/
theorem permField_add (σ : Equiv.Perm (Fin k)) (u v : Field ν k) :
    permField σ (u + v) = permField σ u + permField σ v := rfl

/-- `permField σ` commutes with subtraction. -/
theorem permField_sub (σ : Equiv.Perm (Fin k)) (u v : Field ν k) :
    permField σ (u - v) = permField σ u - permField σ v := rfl

/-- `permField σ` commutes with negation. -/
theorem permField_neg (σ : Equiv.Perm (Fin k)) (u : Field ν k) :
    permField σ (-u) = -permField σ u := rfl

/-- `permField σ` is homogeneous. -/
theorem permField_smul (σ : Equiv.Perm (Fin k)) (c : ℝ) (u : Field ν k) :
    permField σ (c • u) = c • permField σ u := rfl

/-- `permField σ` commutes with finite sums. -/
theorem permField_sum {ι : Type*} (σ : Equiv.Perm (Fin k)) (s : Finset ι) (f : ι → Field ν k) :
    permField σ (∑ i ∈ s, f i) = ∑ i ∈ s, permField σ (f i) := by
  funext I
  simp [Finset.sum_apply]

/-- `symField q` is additive. -/
theorem symField_add (q : ℕ) (u v : Field ν k) :
    symField q (u + v) = symField q u + symField q v := by
  simp only [symField, permField_add, sum_add_distrib, smul_add]

/-- `symField q` commutes with subtraction. -/
theorem symField_sub (q : ℕ) (u v : Field ν k) :
    symField q (u - v) = symField q u - symField q v := by
  simp only [symField, permField_sub, sum_sub_distrib, smul_sub]

/-- `symField q` is homogeneous. -/
theorem symField_smul (q : ℕ) (c : ℝ) (u : Field ν k) :
    symField q (c • u) = c • symField q u := by
  simp only [symField, permField_smul, ← smul_sum, smul_comm c]

/-! ### `normSq` as a squared norm -/

/-- `normSq u` is the squared norm of `u` in `PiLp 2`. -/
theorem normSq_eq_norm_toLp_sq (u : Field ν k) :
    normSq u = ‖(WithLp.toLp 2 u :
      PiLp 2 fun _ : Fin k → Fin (Module.finrank ℝ V) => Lp ℝ 2 (ν : Measure V))‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

/-- The Hilbert–Schmidt norm `√(normSq u)` is the norm of `u` in `PiLp 2`. -/
private theorem sqrt_normSq_eq (u : Field ν k) :
    √(normSq u) = ‖(WithLp.toLp 2 u :
      PiLp 2 fun _ : Fin k → Fin (Module.finrank ℝ V) => Lp ℝ 2 (ν : Measure V))‖ := by
  rw [normSq_eq_norm_toLp_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The triangle inequality for the Hilbert–Schmidt norm `√(normSq ·)`. -/
theorem sqrt_normSq_add_le (u v : Field ν k) :
    √(normSq (u + v)) ≤ √(normSq u) + √(normSq v) := by
  simp only [sqrt_normSq_eq, WithLp.toLp_add]
  exact norm_add_le _ _

/-- Homogeneity of the Hilbert–Schmidt norm `√(normSq ·)`. -/
theorem sqrt_normSq_smul (c : ℝ) (u : Field ν k) :
    √(normSq (c • u)) = |c| * √(normSq u) := by
  simp only [sqrt_normSq_eq, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

/-- The triangle inequality for finite sums in the Hilbert–Schmidt norm `√(normSq ·)`. -/
theorem sqrt_normSq_sum_le {ι : Type*} (s : Finset ι) (f : ι → Field ν k) :
    √(normSq (∑ i ∈ s, f i)) ≤ ∑ i ∈ s, √(normSq (f i)) := by
  simp only [sqrt_normSq_eq, WithLp.toLp_sum]
  exact norm_sum_le _ _

/-- `normSq` is invariant under negation. -/
theorem normSq_neg (u : Field ν k) : normSq (-u) = normSq u := by
  simp [normSq]

/-- `permField σ` preserves the squared Hilbert–Schmidt norm. -/
theorem normSq_permField (σ : Equiv.Perm (Fin k)) (u : Field ν k) :
    normSq (permField σ u) = normSq u := by
  unfold normSq
  exact (Equiv.arrowCongr σ.symm (Equiv.refl (Fin (Module.finrank ℝ V)))).sum_comp
    fun J => ‖u J‖ ^ 2

/-! ### The displacement `√(normSq (u - π u))` -/

/-- Subadditivity of the displacement: `d(σ τ) ≤ d(σ) + d(τ)`. -/
theorem sqrt_normSq_sub_permField_mul_le (σ τ : Equiv.Perm (Fin k)) (u : Field ν k) :
    √(normSq (u - permField (σ * τ) u)) ≤
      √(normSq (u - permField σ u)) + √(normSq (u - permField τ u)) := by
  have h : u - permField (σ * τ) u = (u - permField σ u) + permField σ (u - permField τ u) := by
    rw [permField_sub, permField_mul]
    abel
  rw [h]
  refine (sqrt_normSq_add_le _ _).trans ?_
  rw [normSq_permField]

/-- The displacement of `σ⁻¹` equals that of `σ`. -/
theorem normSq_sub_permField_inv (σ : Equiv.Perm (Fin k)) (u : Field ν k) :
    normSq (u - permField σ⁻¹ u) = normSq (u - permField σ u) := by
  have h : u - permField σ⁻¹ u = -permField σ⁻¹ (u - permField σ u) := by
    rw [permField_sub, ← permField_mul, inv_mul_cancel, permField_one]
    abel
  rw [h, normSq_neg, normSq_permField]

/-- Membership in the permutations of the first `p` positions. -/
theorem mem_fixingOutside_slots_zero {p : ℕ} {σ : Equiv.Perm (Fin k)} :
    σ ∈ fixingOutside (slots k 0 p) ↔ ∀ x : Fin k, p ≤ x.val → σ x = x := by
  simp only [fixingOutside, slots, mem_filter, mem_univ, true_and, zero_le, not_lt]

/-- `finRotate k ℓ = ℓ + 1` below the last position. -/
private theorem val_finRotate_of_lt {ℓ : Fin k} (h : ℓ.val + 1 < k) :
    (finRotate k ℓ).val = ℓ.val + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have := finRotate_of_lt (n := m) (k := ℓ.val) (by omega)
  rw [show ℓ = ⟨ℓ.val, ℓ.val.lt_succ_of_lt (by omega)⟩ from rfl, this]

/-- A chain of adjacent transpositions moving position `a` up to position `b`: some
permutation of the first `b + 1` positions sends `a` to `b` with displacement at most
`(b - a) B`, if every adjacent transposition `τ_ℓ` with `ℓ + 1 < q` has displacement at most
`B`. -/
private theorem exists_chain {q : ℕ} (u : Field ν k) {B : ℝ}
    (hB : ∀ ℓ : Fin k, ℓ.val + 1 < q →
      √(normSq (u - permField (Equiv.swap ℓ (finRotate k ℓ)) u)) ≤ B) :
    ∀ (n : ℕ) (a b : Fin k), b.val = a.val + n → b.val < q →
      ∃ ρ ∈ fixingOutside (slots k 0 (b.val + 1)), ρ a = b ∧
        √(normSq (u - permField ρ u)) ≤ n * B := by
  intro n
  induction n with
  | zero =>
    intro a b hab _
    have : b = a := Fin.ext (by simpa using hab)
    subst this
    refine ⟨1, mem_fixingOutside_slots_zero.mpr fun _ _ => rfl, rfl, ?_⟩
    simp [normSq]
  | succ n ih =>
    intro a b hab hbq
    set b' : Fin k := ⟨b.val - 1, by omega⟩ with hb'
    obtain ⟨ρ', hρ'mem, hρ'a, hρ'd⟩ := ih a b' (by simp [hb']; omega) (by simp [hb']; omega)
    have hrot : finRotate k b' = b := Fin.ext (by
      rw [val_finRotate_of_lt (by simp [hb']; omega)]; simp [hb']; omega)
    refine ⟨Equiv.swap b' b * ρ', ?_, ?_, ?_⟩
    · rw [mem_fixingOutside_slots_zero] at hρ'mem ⊢
      intro x hx
      have hxb' : x ≠ b' := fun h => by subst h; simp [hb'] at hx; omega
      have hxb : x ≠ b := fun h => by subst h; omega
      rw [Equiv.Perm.mul_apply, hρ'mem x (by simp [hb'] at hx ⊢; omega),
        Equiv.swap_apply_of_ne_of_ne hxb' hxb]
    · rw [Equiv.Perm.mul_apply, hρ'a, Equiv.swap_apply_left]
    · refine (sqrt_normSq_sub_permField_mul_le _ _ u).trans ?_
      have h1 := hB b' (by simp [hb']; omega)
      rw [hrot] at h1
      push_cast
      linarith

/-- **Word length bound for the displacement.** If every adjacent transposition `τ_ℓ`
(`ℓ + 1 < q`) moves `u` by at most `B` in the Hilbert–Schmidt norm, then every permutation of
the first `q` positions moves `u` by at most `q² B`. -/
theorem sqrt_normSq_sub_permField_le_of_adjacent {q : ℕ} (hq : q ≤ k) (u : Field ν k) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ ℓ : Fin k, ℓ.val + 1 < q →
      √(normSq (u - permField (Equiv.swap ℓ (finRotate k ℓ)) u)) ≤ B)
    {σ : Equiv.Perm (Fin k)} (hσ : σ ∈ fixingOutside (slots k 0 q)) :
    √(normSq (u - permField σ u)) ≤ (q : ℝ) ^ 2 * B := by
  suffices ∀ p ≤ q, ∀ σ ∈ fixingOutside (slots k 0 p),
      √(normSq (u - permField σ u)) ≤ (p : ℝ) ^ 2 * B from this q le_rfl σ hσ
  intro p
  induction p with
  | zero =>
    intro _ σ hσ
    have : σ = 1 := Equiv.ext fun x => mem_fixingOutside_slots_zero.mp hσ x (Nat.zero_le _)
    subst this
    simp [normSq]
  | succ p ih =>
    intro hpq σ hσ
    rw [mem_fixingOutside_slots_zero] at hσ
    set b : Fin k := ⟨p, by omega⟩ with hb
    have hbv : b.val = p := rfl
    have ha : (σ b).val ≤ p := by
      by_contra h
      have hfix := hσ (σ b) (by omega)
      have : σ b = b := σ.injective hfix
      rw [this] at h
      simp [hb] at h
    obtain ⟨ρ, hρmem, hρa, hρd⟩ :=
      exists_chain u hB (p - (σ b).val) (σ b) b (by rw [hbv]; omega) (by rw [hbv]; omega)
    rw [mem_fixingOutside_slots_zero] at hρmem
    have hσ' : ρ * σ ∈ fixingOutside (slots k 0 p) := by
      rw [mem_fixingOutside_slots_zero]
      intro x hx
      rcases eq_or_ne x b with rfl | hxb
      · rw [Equiv.Perm.mul_apply, hρa]
      · have hx' : p + 1 ≤ x.val := by
          have : x.val ≠ p := fun h => hxb (Fin.ext (by simp [hb, h]))
          omega
        rw [Equiv.Perm.mul_apply, hσ x hx', hρmem x (by simp [hb]; omega)]
    have hdecomp : σ = ρ⁻¹ * (ρ * σ) := by group
    have h1 := sqrt_normSq_sub_permField_mul_le ρ⁻¹ (ρ * σ) u
    rw [← hdecomp, normSq_sub_permField_inv] at h1
    have h2 := ih (by omega) _ hσ'
    have h3 : ((p - (σ b).val : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le _ _
    have h4 : ((p - (σ b).val : ℕ) : ℝ) * B ≤ p * B := mul_le_mul_of_nonneg_right h3 hB0
    have h5 : (p : ℝ) * B + (p : ℝ) ^ 2 * B ≤ ((p + 1 : ℕ) : ℝ) ^ 2 * B := by
      push_cast
      nlinarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
    linarith

/-! ### The bound (44) -/

/-- The sum `Σ_{ℓ+1<q} ‖u - τ_ℓ u‖²` dominates each of its terms' square roots. -/
private theorem sqrt_normSq_adjacent_le {q : ℕ} (u : Field ν k) (ℓ : Fin k) (hℓ : ℓ.val + 1 < q) :
    √(normSq (u - permField (Equiv.swap ℓ (finRotate k ℓ)) u)) ≤
      √(∑ m ∈ univ.filter (fun m : Fin k => m.val + 1 < q),
        normSq (u - permField (Equiv.swap m (finRotate k m)) u)) :=
  Real.sqrt_le_sqrt <| single_le_sum (f := fun m : Fin k =>
      normSq (u - permField (Equiv.swap m (finRotate k m)) u))
    (fun _ _ => normSq_nonneg _) (by simp [hℓ])

/-- **BKL (44), first half.** For every permutation `π` of the first `q` positions,
`‖u - π u‖² ≤ q⁴ Σ_{ℓ+1<q} ‖u - τ_ℓ u‖²`, where `τ_ℓ` swaps positions `ℓ` and `ℓ + 1`. -/
theorem normSq_sub_permField_le {q : ℕ} (hq : q ≤ k) (u : Field ν k) {σ : Equiv.Perm (Fin k)}
    (hσ : σ ∈ fixingOutside (slots k 0 q)) :
    normSq (u - permField σ u) ≤
      (q : ℝ) ^ 4 * ∑ ℓ ∈ univ.filter (fun ℓ : Fin k => ℓ.val + 1 < q),
        normSq (u - permField (Equiv.swap ℓ (finRotate k ℓ)) u) := by
  set S := ∑ ℓ ∈ univ.filter (fun ℓ : Fin k => ℓ.val + 1 < q),
    normSq (u - permField (Equiv.swap ℓ (finRotate k ℓ)) u)
  have hS : 0 ≤ S := sum_nonneg fun _ _ => normSq_nonneg _
  have h := sqrt_normSq_sub_permField_le_of_adjacent hq u (Real.sqrt_nonneg S)
    (fun ℓ hℓ => sqrt_normSq_adjacent_le u ℓ hℓ) hσ
  have h' := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt (normSq_nonneg _), mul_pow, Real.sq_sqrt hS, ← pow_mul] at h'
  exact h'

/-- `u - S_q u` is the average of the displacements `u - π u` over the permutations `π` of the
first `q` positions. -/
private theorem sub_symField_eq (q : ℕ) (u : Field ν k) :
    u - symField q u = ((fixingOutside (slots k 0 q)).card : ℝ)⁻¹ •
      ∑ σ ∈ fixingOutside (slots k 0 q), (u - permField σ u) := by
  have hne : ((fixingOutside (slots k 0 q)).card : ℝ) ≠ 0 := by
    have : (1 : Equiv.Perm (Fin k)) ∈ fixingOutside (slots k 0 q) :=
      mem_fixingOutside_slots_zero.mpr fun _ _ => rfl
    exact_mod_cast (card_pos.mpr ⟨1, this⟩).ne'
  rw [sum_sub_distrib, sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, inv_smul_smul₀ hne]
  rfl

/-- **BKL Lemma 3.3, (44).** For `q ≤ k` and a tensor field `u` with `k` indices,
`‖u - S_q u‖² ≤ q⁴ Σ_{ℓ+1<q} ‖u - τ_ℓ u‖²`, where `S_q` averages over the permutations of the
first `q` index positions and `τ_ℓ` swaps positions `ℓ` and `ℓ + 1`. -/
theorem normSq_sub_symField_le {q : ℕ} (hq : q ≤ k) (u : Field ν k) :
    normSq (u - symField q u) ≤
      (q : ℝ) ^ 4 * ∑ ℓ ∈ univ.filter (fun ℓ : Fin k => ℓ.val + 1 < q),
        normSq (u - permField (Equiv.swap ℓ (finRotate k ℓ)) u) := by
  set S := ∑ ℓ ∈ univ.filter (fun ℓ : Fin k => ℓ.val + 1 < q),
    normSq (u - permField (Equiv.swap ℓ (finRotate k ℓ)) u)
  set G := fixingOutside (slots k 0 q)
  have hS : 0 ≤ S := sum_nonneg fun _ _ => normSq_nonneg _
  have hG : (0 : ℝ) < G.card := by
    have : (1 : Equiv.Perm (Fin k)) ∈ G := mem_fixingOutside_slots_zero.mpr fun _ _ => rfl
    exact_mod_cast card_pos.mpr ⟨1, this⟩
  have hbound : √(normSq (u - symField q u)) ≤ (q : ℝ) ^ 2 * √S := by
    rw [sub_symField_eq, sqrt_normSq_smul, abs_of_pos (inv_pos.mpr hG)]
    calc (G.card : ℝ)⁻¹ * √(normSq (∑ σ ∈ G, (u - permField σ u)))
        ≤ (G.card : ℝ)⁻¹ * ∑ σ ∈ G, √(normSq (u - permField σ u)) :=
          mul_le_mul_of_nonneg_left (sqrt_normSq_sum_le _ _) (inv_nonneg.mpr hG.le)
      _ ≤ (G.card : ℝ)⁻¹ * ∑ _σ ∈ G, (q : ℝ) ^ 2 * √S := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun σ hσ => ?_) (inv_nonneg.mpr hG.le)
          exact sqrt_normSq_sub_permField_le_of_adjacent hq u (Real.sqrt_nonneg S)
            (fun ℓ hℓ => sqrt_normSq_adjacent_le u ℓ hℓ) hσ
      _ = (q : ℝ) ^ 2 * √S := by
          rw [sum_const, nsmul_eq_mul, inv_mul_cancel_left₀ hG.ne']
  have h' := pow_le_pow_left₀ (Real.sqrt_nonneg _) hbound 2
  rw [Real.sq_sqrt (normSq_nonneg _), mul_pow, Real.sq_sqrt hS, ← pow_mul] at h'
  exact h'

end FunctionalInequalities.KLS.LogConcave.PoissonIterate
