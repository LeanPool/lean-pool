/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.PoissonIterate.Taylor
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.PoissonIterate.Symmetry

/-!
# Lemma 3.8 of BKL for the iterates in `D(A)`

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Lemma 3.8, pp. 15–16, (55)–(59), for the iterates
`iter Tbar f k` (the source's `h_{k+1}`) of `PoissonIterate/Basic.lean` in the heat model
`ν = m.tilted (-U)`, `U` of temperate growth with all exponential moments, `Tbar` the closed
unit-weight gradient, `A = Tbar†Tbar = -ℒ` and `C_P(ν) ≤ C` with `0 < C`. Coefficient arrays are
taken
in `stdOrthonormalBasis ℝ V`, with the Hilbert–Schmidt norm; `taylorField d u` puts the `d` Taylor
indices first.

## What is proved

* `norm_symmetrize_taylorField_grad0_iter_sq_le`: **(56)–(57)**, iterating Corollary 3.7: if
  `α_{j+2}² ≤ β/C` for `j < k` and `e ≤ k`, `d ≥ 1`, then
  `|S_{d+e} T_d(∇₀h_{k+1})|² ≤ (β/C)^e |T_{d+e}(∇₀h_{k+1-e})|²`;
* `norm_taylorField_grad0_iter_sq_le`: **BKL Lemma 3.8** in the form used here: under the Taylor
  bound (29) `|T_d g| ≤ R^d ‖g‖` for `d ≥ 1`, for `d ≥ 1`, `2d ≤ k + 1` and
  `0 < α_{j+2}² ≤ β/C` for `j < k`,
  `|T_d(∇₀h_{k+1})|² ≤ (c/C)^d |T_{2d}(∇₀h_{k+1-d})|² + c^d R^{2d} C Σ_{k+1-2d ≤ j < k} χ_{j+1}`
  with the explicit constant `c = 2^20 max(1, β)²`.

Generic facts on the way (private): an average over a permutation group is a contraction, is
linear, absorbs the average over a subgroup (`S_{q'} S_q = S_{q'}` for `q ≤ q'`) and is invariant
under the group; `S_q` commutes with relabelling the positions along `N = N'`; `T_d` is additive
on `L²` classes; the Taylor indices of `T_d u` are symmetric; and (29) componentwise,
`|T_d u|² ≤ R^{2d} ‖u‖²` for a tensor field `u`.

## The argument

Write `T = T_d(∇₀h_{k+1})` and `Ttilde = T_d(S_{2d} ∇₀h_{k+1})`. Since
`S_{d+e+1} = S_{d+e+1} S_{d+1}`
and `S_{d+1} T_d(∇₀h_{k+2}) = α_{k+2} T_{d+1}(∇₀h_{k+1})` (Corollary 3.7), induction on `e` gives
(56)–(57), and with `e = d`, `|S_{2d} T|² ≤ (β/C)^d |T_{2d}(∇₀h_{k+1-d})|²`. The tensor `Ttilde` has
`d + k + 1 ≥ 3d` indices and is symmetric in its first `d` (Taylor) and its next `2d` indices, so
Lemma 2.2 gives `|Ttilde| ≤ 4^d |S_{2d} Ttilde| ≤ 4^d (|S_{2d} T| + |T - Ttilde|)`. By linearity
`T - Ttilde = T_d(∇₀h_{k+1} - S_{2d} ∇₀h_{k+1})`, so (29) and Lemma 3.3 with `q = 2d` bound
`|T - Ttilde|² ≤ R^{2d} · 4 (2d)⁴ max(1, β)^{2d} C Σ χ`. Then (59):
`|T|² ≤ 2 (1 + 4^d)² |T - Ttilde|² + 2 · 16^d |S_{2d} T|²`, and `2 · 16^d β^d ≤ c^d`,
`2 (1 + 4^d)² · 4 (2d)⁴ max(1, β)^{2d} ≤ c^d` for `d ≥ 1`.

## What this is not

The constant `c` is explicit, not the source's unspecified
universal constant; the bound (29) is used only for `d` itself, and `R ≥ 1` and the centering of
`f` are not needed. Lemma 3.9's bound by `R` and Theorem 3.1 are not proved here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ContDiff

namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate

/-! ### Averages over the permutations fixing the outside of a set -/

section Block

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

private theorem one_mem_fixingOutside' (s : Finset Ω) :
    (1 : Equiv.Perm Ω) ∈ fixingOutside s := by
  simp [fixingOutside]

private theorem sum_fixingOutside_mul_right {M : Type*} [AddCommMonoid M] {s : Finset Ω}
    {τ : Equiv.Perm Ω} (hτ : τ ∈ fixingOutside s) (g : Equiv.Perm Ω → M) :
    ∑ σ ∈ fixingOutside s, g (σ * τ) = ∑ σ ∈ fixingOutside s, g σ :=
  sum_nbij' (· * τ) (· * τ⁻¹) (fun _ hσ => mul_mem_fixingOutside hσ hτ)
    (fun _ hσ => mul_mem_fixingOutside hσ (inv_mem_fixingOutside hτ))
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => rfl)

private theorem sum_fixingOutside_mul_left {M : Type*} [AddCommMonoid M] {s : Finset Ω}
    {τ : Equiv.Perm Ω} (hτ : τ ∈ fixingOutside s) (g : Equiv.Perm Ω → M) :
    ∑ σ ∈ fixingOutside s, g (τ * σ) = ∑ σ ∈ fixingOutside s, g σ :=
  sum_nbij' (τ * ·) (τ⁻¹ * ·) (fun _ hσ => mul_mem_fixingOutside hτ hσ)
    (fun _ hσ => mul_mem_fixingOutside (inv_mem_fixingOutside hτ) hσ)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => rfl)

private theorem card_fixingOutside_pos (s : Finset Ω) : (0 : ℝ) < (fixingOutside s).card := by
  exact_mod_cast card_pos.mpr ⟨1, one_mem_fixingOutside' s⟩

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

private theorem norm_blockAverage_le (ρ : Equiv.Perm Ω →* (W ≃ₗᵢ[ℝ] W)) (s : Finset Ω) (v : W) :
    ‖blockAverage ρ s v‖ ≤ ‖v‖ := by
  have hG := card_fixingOutside_pos s
  rw [blockAverage, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hG)]
  calc ((fixingOutside s).card : ℝ)⁻¹ * ‖∑ σ ∈ fixingOutside s, ρ σ v‖
      ≤ ((fixingOutside s).card : ℝ)⁻¹ * ∑ σ ∈ fixingOutside s, ‖ρ σ v‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hG.le)
    _ = ‖v‖ := by
        simp only [LinearIsometryEquiv.norm_map, sum_const, nsmul_eq_mul]
        rw [inv_mul_cancel_left₀ hG.ne']

private theorem blockAverage_sub (ρ : Equiv.Perm Ω →* (W ≃ₗᵢ[ℝ] W)) (s : Finset Ω) (v w : W) :
    blockAverage ρ s (v - w) = blockAverage ρ s v - blockAverage ρ s w := by
  simp only [blockAverage, map_sub, sum_sub_distrib, smul_sub]

private theorem blockAverage_smul (ρ : Equiv.Perm Ω →* (W ≃ₗᵢ[ℝ] W)) (s : Finset Ω) (c : ℝ)
    (v : W) : blockAverage ρ s (c • v) = c • blockAverage ρ s v := by
  simp only [blockAverage, map_smul, ← smul_sum, smul_comm c]

/-- Averaging over a group absorbs the average over a subgroup. -/
private theorem blockAverage_blockAverage (ρ : Equiv.Perm Ω →* (W ≃ₗᵢ[ℝ] W)) {s t : Finset Ω}
    (hst : s ⊆ t) (v : W) : blockAverage ρ t (blockAverage ρ s v) = blockAverage ρ t v := by
  have hG := card_fixingOutside_pos s
  have hmul : ∀ σ τ : Equiv.Perm Ω, ρ σ (ρ τ v) = ρ (σ * τ) v := fun σ τ => by
    rw [map_mul]
    rfl
  simp only [blockAverage, map_smul, map_sum, hmul]
  congr 1
  rw [← smul_sum, sum_comm]
  have h : ∀ τ ∈ fixingOutside s,
      ∑ σ ∈ fixingOutside t, ρ (σ * τ) v = ∑ σ ∈ fixingOutside t, ρ σ v := fun τ hτ =>
    sum_fixingOutside_mul_right (fixingOutside_mono hst hτ) (fun σ => ρ σ v)
  rw [sum_congr rfl h, sum_const, ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ hG.ne']

end Block

/-! ### `S_q` on coordinate tensors -/

section Coordinates

variable {n N : ℕ}

private theorem slots_zero_subset {q q' : ℕ} (h : q ≤ q') : slots N 0 q ⊆ slots N 0 q' := by
  intro x hx
  simp only [slots, mem_filter, mem_univ, true_and] at hx ⊢
  omega

private theorem norm_symmetrize_le (q : ℕ) (A : Coord n N) : ‖symmetrize n N q A‖ ≤ ‖A‖ :=
  norm_blockAverage_le _ _ _

private theorem symmetrize_sub (q : ℕ) (A B : Coord n N) :
    symmetrize n N q (A - B) = symmetrize n N q A - symmetrize n N q B :=
  blockAverage_sub _ _ _ _

private theorem symmetrize_smul (q : ℕ) (c : ℝ) (A : Coord n N) :
    symmetrize n N q (c • A) = c • symmetrize n N q A :=
  blockAverage_smul _ _ _ _

private theorem symmetrize_symmetrize {q q' : ℕ} (h : q ≤ q') (A : Coord n N) :
    symmetrize n N q' (symmetrize n N q A) = symmetrize n N q' A :=
  blockAverage_blockAverage _ (slots_zero_subset h) A

/-- Relabelling the index positions of a coordinate tensor along `N = N'`. -/
private def recast {N' : ℕ} (h : N = N') (A : Coord n N) : Coord n N' :=
  WithLp.toLp 2 fun J => A (J ∘ Fin.cast h)

private theorem recast_rfl (A : Coord n N) : recast rfl A = A := by
  ext J
  simp [recast]

private theorem norm_recast {N' : ℕ} (h : N = N') (A : Coord n N) : ‖recast h A‖ = ‖A‖ := by
  subst h
  rw [recast_rfl]

private theorem symmetrize_recast {N' : ℕ} (h : N = N') (q : ℕ) (A : Coord n N) :
    symmetrize n N' q (recast h A) = recast h (symmetrize n N q A) := by
  subst h
  rw [recast_rfl, recast_rfl]

end Coordinates

/-! ### Permutations of a block of positions -/

section Perm

/-- A permutation of `Fin (a + b)` fixing the first `a` positions permutes the last `b`. -/
private theorem exists_perm_natAdd {a b : ℕ} (σ : Equiv.Perm (Fin (a + b)))
    (hσ : ∀ i : Fin a, σ (Fin.castAdd b i) = Fin.castAdd b i) :
    ∃ π : Equiv.Perm (Fin b), ∀ i, σ (Fin.natAdd a i) = Fin.natAdd a (π i) := by
  have hge : ∀ i : Fin b, a ≤ (σ (Fin.natAdd a i) : ℕ) := by
    intro i
    by_contra hc
    rw [not_le] at hc
    have h1 : σ (Fin.natAdd a i) = σ (Fin.castAdd b ⟨_, hc⟩) := by
      rw [hσ]
      exact Fin.ext rfl
    have h2 := congrArg Fin.val (σ.injective h1)
    simp at h2
    omega
  let g : Fin b → Fin b := fun i =>
    ⟨(σ (Fin.natAdd a i) : ℕ) - a, by have := (σ (Fin.natAdd a i)).isLt; have := i.isLt; omega⟩
  have hg_spec : ∀ i, σ (Fin.natAdd a i) = Fin.natAdd a (g i) := by
    intro i
    apply Fin.ext
    simp only [Fin.val_natAdd, g]
    have := hge i
    omega
  have hg : Function.Injective g := by
    intro i j hij
    have h : σ (Fin.natAdd a i) = σ (Fin.natAdd a j) := by rw [hg_spec, hg_spec, hij]
    have h' := congrArg Fin.val (σ.injective h)
    simp only [Fin.val_natAdd, Nat.add_left_cancel_iff] at h'
    exact Fin.ext h'
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg), hg_spec⟩

/-- A permutation of `Fin (a + b)` fixing the last `b` positions permutes the first `a`. -/
private theorem exists_perm_castAdd {a b : ℕ} (σ : Equiv.Perm (Fin (a + b)))
    (hσ : ∀ i : Fin b, σ (Fin.natAdd a i) = Fin.natAdd a i) :
    ∃ π : Equiv.Perm (Fin a), ∀ i, σ (Fin.castAdd b i) = Fin.castAdd b (π i) := by
  have hlt : ∀ i : Fin a, (σ (Fin.castAdd b i) : ℕ) < a := by
    intro i
    by_contra hc
    rw [not_lt] at hc
    have hb : (σ (Fin.castAdd b i) : ℕ) - a < b := by
      have := (σ (Fin.castAdd b i)).isLt
      omega
    have h1 : σ (Fin.castAdd b i) = σ (Fin.natAdd a ⟨_, hb⟩) := by
      rw [hσ]
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
    have h2 := congrArg Fin.val (σ.injective h1)
    simp at h2
    omega
  let g : Fin a → Fin a := fun i => ⟨σ (Fin.castAdd b i), hlt i⟩
  have hg_spec : ∀ i, σ (Fin.castAdd b i) = Fin.castAdd b (g i) := fun i => Fin.ext rfl
  have hg : Function.Injective g := by
    intro i j hij
    have h : σ (Fin.castAdd b i) = σ (Fin.castAdd b j) := by rw [hg_spec, hg_spec, hij]
    have h' := congrArg Fin.val (σ.injective h)
    simp only [Fin.val_castAdd] at h'
    exact Fin.ext h'
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg), hg_spec⟩

end Perm

/-! ### Taylor arrays of tensor fields -/

section Taylor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : ProbabilityMeasure V}
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))

include hexp in
/-- `T_d` is additive on `L²(ν)` classes. -/
private theorem taylorTensor_Lp_sub (u v : Lp ℝ 2 (ν : Measure V)) (d : ℕ) :
    taylorTensor (ν : Measure V) (⇑(u - v)) d =
      taylorTensor (ν : Measure V) (⇑u) d - taylorTensor (ν : Measure V) (⇑v) d := by
  have h1 : (⇑(u - v)) =ᵐ[(ν : Measure V)] fun x => u x + (-1 : ℝ) * v x := by
    filter_upwards [Lp.coeFn_sub u v] with x hx
    rw [hx, Pi.sub_apply]
    ring
  rw [taylorTensor_congr_ae _ h1 d,
    taylorTensor_add _ hexp (Lp.memLp u) ((Lp.memLp v).const_mul (-1)) d,
    taylorTensor_const_mul, neg_one_smul, sub_eq_add_neg]

include hexp in
/-- `taylorField d` is additive. -/
private theorem taylorField_sub (d : ℕ) {k : ℕ} (u v : Field ν k) :
    taylorField d (u - v) = taylorField d u - taylorField d v := by
  ext J
  simp only [taylorField, PiLp.toLp_apply, Pi.sub_apply, taylorTensor_Lp_sub hexp,
    PiLp.sub_apply]
  rfl

include hexp in
/-- The Taylor tensors of an `L²` class are symmetric. -/
private theorem taylorTensor_Lp_comp_perm (g : Lp ℝ 2 (ν : Measure V)) {d : ℕ}
    (π : Equiv.Perm (Fin d)) (v : Fin d → V) :
    taylorTensor (ν : Measure V) (⇑g) d (v ∘ π) = taylorTensor (ν : Measure V) (⇑g) d v := by
  have h := congrArg (fun Φ => Φ v) (taylorTensor_domDomCongr (ν : Measure V) (⇑g)
    (contDiff_tiltAverage_of_memLp (ν : Measure V) hexp (Lp.memLp g)) d π)
  simp only [ContinuousMultilinearMap.domDomCongr_apply] at h
  exact h

include hexp in
/-- `taylorField d u` is symmetric in its first `d` (Taylor) index positions. -/
private theorem slotRep_taylorField_left {d k : ℕ} (u : Field ν k)
    {σ : Equiv.Perm (Fin (d + k))} (hσ : σ ∈ fixingOutside (slots (d + k) 0 d)) :
    slotRep (Module.finrank ℝ V) (d + k) σ (taylorField d u) = taylorField d u := by
  simp only [fixingOutside, mem_filter, mem_univ, true_and] at hσ
  have hfix : ∀ i : Fin k, σ (Fin.natAdd d i) = Fin.natAdd d i :=
    fun i => hσ _ (by simp [slots])
  obtain ⟨π, hπ⟩ := exists_perm_castAdd σ hfix
  ext J
  change slotPerm _ _ σ (taylorField d u) J = _
  rw [slotPerm_apply]
  simp only [taylorField, PiLp.toLp_apply, Function.comp_apply, hfix, hπ]
  exact taylorTensor_Lp_comp_perm hexp _ π (fun i => stdOrthonormalBasis ℝ V (J (Fin.castAdd k i)))

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- `S_q u` is invariant under the permutations of the first `q` positions. -/
private theorem permField_symField {k q : ℕ} (u : Field ν k) {π : Equiv.Perm (Fin k)}
    (hπ : π ∈ fixingOutside (slots k 0 q)) : permField π (symField q u) = symField q u := by
  rw [symField, permField_smul, permField_sum]
  congr 1
  simp only [← permField_mul]
  exact sum_fixingOutside_mul_left hπ (fun σ => permField σ u)

section TaylorFieldBounds

omit [BorelSpace V]
/-- `taylorField d u` is symmetric in the `q` positions after the Taylor indices when `u` is
symmetric in its first `q` positions. -/
private theorem slotRep_taylorField_right {d k q : ℕ} (u : Field ν k)
    (hu : ∀ π ∈ fixingOutside (slots k 0 q), permField π u = u) {σ : Equiv.Perm (Fin (d + k))}
    (hσ : σ ∈ fixingOutside (slots (d + k) d (d + q))) :
    slotRep (Module.finrank ℝ V) (d + k) σ (taylorField d u) = taylorField d u := by
  simp only [fixingOutside, mem_filter, mem_univ, true_and] at hσ
  have hfix : ∀ i : Fin d, σ (Fin.castAdd k i) = Fin.castAdd k i :=
    fun i => hσ _ (by simp [slots])
  obtain ⟨π, hπ⟩ := exists_perm_natAdd σ hfix
  have hπmem : π ∈ fixingOutside (slots k 0 q) := by
    simp only [fixingOutside, mem_filter, mem_univ, true_and]
    intro i hi
    have h := hσ (Fin.natAdd d i) (by simp [slots] at hi ⊢; omega)
    rw [hπ] at h
    have h' := congrArg Fin.val h
    simp only [Fin.val_natAdd, Nat.add_left_cancel_iff] at h'
    exact Fin.ext h'
  ext J
  change slotPerm _ _ σ (taylorField d u) J = _
  rw [slotPerm_apply]
  simp only [taylorField, PiLp.toLp_apply, Function.comp_apply, hfix, hπ]
  have h := congrFun (hu π hπmem) (fun i => J (Fin.natAdd d i))
  rw [permField_apply] at h
  rw [show (fun i => J (Fin.natAdd d (π i))) = (fun i => J (Fin.natAdd d i)) ∘ π from rfl, h]

/-- **The Taylor bound (29) componentwise**: if `|T_d g| ≤ R^d ‖g‖₂` for every `g ∈ L²(ν)`, then
`|T_d u|² ≤ R^{2d} ‖u‖²` for every tensor field `u`. -/
theorem norm_taylorField_sq_le {R : ℝ} {d : ℕ}
    (h29 : ∀ g : Lp ℝ 2 (ν : Measure V),
      ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑g) d)‖ ≤
        R ^ d * ‖g‖) {k : ℕ} (u : Field ν k) :
    ‖taylorField d u‖ ^ 2 ≤ R ^ (2 * d) * normSq u := by
  rw [EuclideanSpace.norm_sq_eq, ← (Fin.appendEquiv d k).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm, normSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun I _ => ?_
  have hI : ∑ J : Fin d → Fin (Module.finrank ℝ V),
      ‖taylorField d u (Fin.appendEquiv d k (J, I))‖ ^ 2 =
        ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑(u I)) d)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun J _ => ?_
    simp [taylorField, coordTensor_apply, Fin.append_left, Fin.append_right]
  rw [hI, pow_mul', ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h29 (u I)) 2

end TaylorFieldBounds

end Taylor

/-! ### The constants -/

section Constants

private theorem two_le_two_pow {d : ℕ} (hd : 1 ≤ d) : (2 : ℝ) ≤ 2 ^ d := by
  calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd

private theorem const_bound_one {β : ℝ} (hβ : 0 ≤ β) {d : ℕ} (hd : 1 ≤ d) :
    2 * 16 ^ d * β ^ d ≤ (2 ^ 20 * max 1 β ^ 2) ^ d := by
  have hM : β ≤ max 1 β ^ 2 := by
    have h1 : (1 : ℝ) ≤ max 1 β := le_max_left _ _
    nlinarith [le_max_right 1 β]
  have h16 : 2 * (16 : ℝ) ^ d ≤ (2 ^ 20) ^ d :=
    calc 2 * (16 : ℝ) ^ d ≤ 2 ^ d * 16 ^ d :=
          mul_le_mul_of_nonneg_right (two_le_two_pow hd) (by positivity)
      _ = 32 ^ d := by rw [← mul_pow]; norm_num
      _ ≤ (2 ^ 20) ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
  rw [mul_pow]
  exact mul_le_mul h16 (pow_le_pow_left₀ hβ hM d) (by positivity) (by positivity)

private theorem const_bound_two (β : ℝ) {d : ℕ} (hd : 1 ≤ d) :
    2 * (1 + 4 ^ d) ^ 2 * (4 * ((2 * d : ℕ) : ℝ) ^ 4 * max 1 β ^ (2 * d)) ≤
      (2 ^ 20 * max 1 β ^ 2) ^ d := by
  have h4 : (1 : ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
  have h44 : ((4 : ℝ) ^ d) ^ 2 = 16 ^ d := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hA : (1 + (4 : ℝ) ^ d) ^ 2 ≤ 4 * 16 ^ d := by nlinarith
  have hdle : (d : ℝ) ≤ 2 ^ d := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hB : ((2 * d : ℕ) : ℝ) ^ 4 ≤ 16 * 16 ^ d := by
    push_cast
    have : (d : ℝ) ^ 4 ≤ (2 ^ d) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hdle 4
    rw [← pow_mul, mul_comm, pow_mul] at this
    norm_num at this
    nlinarith
  have hM : max 1 β ^ (2 * d) = (max 1 β ^ 2) ^ d := pow_mul _ _ _
  have hMp : 0 ≤ (max 1 β ^ 2) ^ d := by positivity
  have h512 : (512 : ℝ) ≤ 4096 ^ d :=
    calc (512 : ℝ) ≤ 4096 ^ 1 := by norm_num
      _ ≤ 4096 ^ d := pow_le_pow_right₀ (by norm_num) hd
  have h16 : (0 : ℝ) ≤ 16 ^ d := by positivity
  calc 2 * (1 + 4 ^ d) ^ 2 * (4 * ((2 * d : ℕ) : ℝ) ^ 4 * max 1 β ^ (2 * d))
      ≤ 2 * (4 * 16 ^ d) * (4 * (16 * 16 ^ d) * (max 1 β ^ 2) ^ d) := by
        rw [hM]
        gcongr
    _ = 512 * (16 ^ d * 16 ^ d) * (max 1 β ^ 2) ^ d := by ring
    _ = 512 * 256 ^ d * (max 1 β ^ 2) ^ d := by rw [← mul_pow]; norm_num
    _ ≤ 4096 ^ d * 256 ^ d * (max 1 β ^ 2) ^ d := by gcongr
    _ = (2 ^ 20 * max 1 β ^ 2) ^ d := by rw [← mul_pow, ← mul_pow]; norm_num

end Constants

/-! ### Lemma 3.8 in the heat model -/

section HeatModel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
  {C : NNReal} (hC : Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal))

local notation "Tbar" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

include hνU hUt hexp hC in
/-- **BKL (56)–(57)**: iterating Corollary 3.7. If `α_{j+2}² ≤ β/C` for `j < k`, `e ≤ k` and
`d ≥ 1`, then `|S_{d+e} T_d(∇₀h_{k+1})|² ≤ (β/C)^e |T_{d+e}(∇₀h_{k+1-e})|²`. -/
theorem norm_symmetrize_taylorField_grad0_iter_sq_le (f : Lp ℝ 2 (ν : Measure V)) {β : ℝ}
    (e : ℕ) :
    ∀ (d k : ℕ),
      1 ≤ d →
        e ≤ k →
          (∀ j < k, scale Tbar (iter Tbar f j) ^ 2 ≤ β / C) →
            ‖symmetrize (Module.finrank ℝ V) (d + (k + 1)) (d + e)
                    (taylorField d (grad0 Tbar (iter Tbar f k)))‖ ^
                2 ≤
              (β / C) ^ e * ‖taylorField (d + e) (grad0 Tbar (iter Tbar f (k - e)))‖ ^ 2 := by
  induction e with
  | zero =>
    intro d k _ _ _
    rw [pow_zero, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_symmetrize_le _ _) 2
  | succ e ih =>
    intro d k hd hk hβ
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [show d + (e + 1) = d + 1 + e by omega, show k + 1 - (e + 1) = k - e by omega]
    have hN : d + (k + 1 + 1) = d + 1 + (k + 1) := by omega
    have hS2 :
      recast hN
          (symmetrize (Module.finrank ℝ V) (d + (k + 1 + 1)) (d + 1)
            (taylorField d (grad0 Tbar (iter Tbar f (k + 1))))) =
        scale Tbar (iter Tbar f k) • taylorField (d + 1) (grad0 Tbar (iter Tbar f k)) := by
      ext J
      simp only [recast, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
      exact
        symmetrize_taylorField_grad0_iter_succ m hν hi hνU
          (hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)) hexp hC f k hd J
    have hnorm :
      ‖symmetrize (Module.finrank ℝ V) (d + (k + 1 + 1)) (d + 1 + e)
            (taylorField d (grad0 Tbar (iter Tbar f (k + 1))))‖ =
        |scale Tbar (iter Tbar f k)| *
          ‖symmetrize (Module.finrank ℝ V) (d + 1 + (k + 1)) (d + 1 + e)
              (taylorField (d + 1) (grad0 Tbar (iter Tbar f k)))‖ := by
      rw [← symmetrize_symmetrize (q := d + 1) (by omega), ← norm_recast hN, ←
        symmetrize_recast, hS2, symmetrize_smul, norm_smul, Real.norm_eq_abs]
    have hα := hβ k (by omega)
    have hβC : 0 ≤ β / C := (sq_nonneg _).trans hα
    have ih' := ih (d + 1) k (by omega) (by omega) fun j hj => hβ j (by omega)
    rw [hnorm, mul_pow, sq_abs, pow_succ]
    calc
      scale Tbar (iter Tbar f k) ^ 2 *
            ‖symmetrize (Module.finrank ℝ V) (d + 1 + (k + 1)) (d + 1 + e)
                  (taylorField (d + 1) (grad0 Tbar (iter Tbar f k)))‖ ^
              2 ≤
          β / C *
            ((β / C) ^ e * ‖taylorField (d + 1 + e) (grad0 Tbar (iter Tbar f (k - e)))‖ ^ 2) :=
        mul_le_mul hα ih' (sq_nonneg _) hβC
      _ = _ := by ring

include hνU hUt hexp hC in
/-- **BKL Lemma 3.8** in the form used here, with the explicit constant `c = 2^20 max(1, β)²`. Under
the Taylor bound (29), `|T_d g| ≤ R^d ‖g‖₂` for `g ∈ L²(ν)` and `d ≥ 1` (Hilbert–Schmidt norm in
the standard basis), for `f ∈ D(A)`, `d ≥ 1`, `2d ≤ k + 1` and `0 < α_{j+2}² ≤ β/C` for `j < k`:
`|T_d(∇₀h_{k+1})|² ≤ (c/C)^d |T_{2d}(∇₀h_{k+1-d})|² + c^d R^{2d} C Σ_{k+1-2d ≤ j < k} χ_{j+1}`. -/
theorem norm_taylorField_grad0_iter_sq_le (hCpos : 0 < C) {R : ℝ}
    (h29 : ∀ (u : Lp ℝ 2 (ν : Measure V)) (d : ℕ), 1 ≤ d →
      ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑u) d)‖ ≤
        R ^ d * ‖u‖)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp Tbar).domain) {β : ℝ} (k d : ℕ)
    (hd : 1 ≤ d) (hdk : 2 * d ≤ k + 1)
    (hα : ∀ j < k, 0 < scale Tbar (iter Tbar f j) ∧ scale Tbar (iter Tbar f j) ^ 2 ≤ β / C) :
    ‖taylorField d (grad0 Tbar (iter Tbar f k))‖ ^ 2 ≤
      (2 ^ 20 * max 1 β ^ 2 / C) ^ d *
          ‖taylorField (2 * d) (grad0 Tbar (iter Tbar f (k - d)))‖ ^ 2 +
        (2 ^ 20 * max 1 β ^ 2) ^ d * R ^ (2 * d) * C *
          ∑ j ∈ Finset.Ico (k + 1 - 2 * d) k, defect Tbar (iter Tbar f j) := by
  have hC0 : (0 : ℝ) < C := hCpos
  -- `β ≥ 0` from the first step
  have hβ : 0 ≤ β := by
    obtain ⟨h0, h1⟩ := hα 0 (by omega)
    have : 0 ≤ β / C := (sq_nonneg _).trans h1
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr hC0)
  set n := Module.finrank ℝ V
  set u := grad0 Tbar (iter Tbar f k)
  set Y := ‖taylorField (2 * d) (grad0 Tbar (iter Tbar f (k - d)))‖ ^ 2
  set D := ∑ j ∈ Finset.Ico (k + 1 - 2 * d) k, defect Tbar (iter Tbar f j)
  set M := max 1 β
  set A : Coord n (d + (k + 1)) := taylorField d u
  set B : Coord n (d + (k + 1)) := taylorField d (symField (2 * d) u)
  set SA := symmetrize n (d + (k + 1)) (2 * d) A
  -- (56)–(57)
  have hS : ‖SA‖ ^ 2 ≤ (β / C) ^ d * Y := by
    have h := norm_symmetrize_taylorField_grad0_iter_sq_le m hν hi hνU hUt hexp hC f d d k hd
      (by omega) fun j hj => (hα j hj).2
    rw [show d + d = 2 * d by ring] at h
    exact h
  -- Lemma 2.2 for `Ttilde = B`
  have hL22 : ‖B‖ ≤ 4 ^ d * ‖symmetrize n (d + (k + 1)) (2 * d) B‖ :=
    norm_le_four_pow_mul_norm_symmetrize (by omega) B
      (fun σ hσ => slotRep_taylorField_left hexp _ hσ)
      (fun σ hσ => slotRep_taylorField_right (q := 2 * d) _
        (fun π hπ => permField_symField _ hπ)
        (by rw [show 3 * d = d + 2 * d by ring] at hσ; exact hσ))
  -- (29) and Lemma 3.3
  have hAB : A - B = taylorField d (u - symField (2 * d) u) := (taylorField_sub hexp d _ _).symm
  have hS1 := normSq_grad0_iter_sub_symField_le m hν hi hνU hUt hexp hC hCpos hf k (2 * d)
    (by omega) hdk fun j _ hj => hα j hj
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun j _ => normSq_nonneg _
  have hR0 : 0 ≤ R ^ (2 * d) := by rw [pow_mul]; positivity
  have hdiff : ‖A - B‖ ^ 2 ≤
      R ^ (2 * d) * (4 * ((2 * d : ℕ) : ℝ) ^ 4 * M ^ (2 * d) * C * D) := by
    rw [hAB]
    exact (norm_taylorField_sq_le (fun g => h29 g d hd) _).trans
      (mul_le_mul_of_nonneg_left hS1 hR0)
  -- (59)
  have htri : ‖A‖ ≤ (1 + 4 ^ d) * ‖A - B‖ + 4 ^ d * ‖SA‖ := by
    have h1 : ‖A‖ ≤ ‖A - B‖ + ‖B‖ := by
      calc ‖A‖ = ‖(A - B) + B‖ := by rw [sub_add_cancel]
        _ ≤ ‖A - B‖ + ‖B‖ := norm_add_le _ _
    have h2 : ‖symmetrize n (d + (k + 1)) (2 * d) B‖ ≤ ‖SA‖ + ‖A - B‖ := by
      have : symmetrize n (d + (k + 1)) (2 * d) B =
          SA - symmetrize n (d + (k + 1)) (2 * d) (A - B) := by
        rw [symmetrize_sub]
        abel
      rw [this]
      exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_symmetrize_le _ _))
    have h4 : (0 : ℝ) ≤ 4 ^ d := by positivity
    nlinarith
  have hsq : ‖A‖ ^ 2 ≤ 2 * (1 + 4 ^ d) ^ 2 * ‖A - B‖ ^ 2 + 2 * 16 ^ d * ‖SA‖ ^ 2 := by
    have h44 : ((4 : ℝ) ^ d) ^ 2 = 16 ^ d := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have h := pow_le_pow_left₀ (norm_nonneg A) htri 2
    calc ‖A‖ ^ 2 ≤ ((1 + 4 ^ d) * ‖A - B‖ + 4 ^ d * ‖SA‖) ^ 2 := h
      _ ≤ 2 * ((1 + 4 ^ d) * ‖A - B‖) ^ 2 + 2 * (4 ^ d * ‖SA‖) ^ 2 := by
          nlinarith [sq_nonneg ((1 + 4 ^ d) * ‖A - B‖ - 4 ^ d * ‖SA‖)]
      _ = 2 * (1 + 4 ^ d) ^ 2 * ‖A - B‖ ^ 2 + 2 * 16 ^ d * ‖SA‖ ^ 2 := by
          rw [mul_pow, mul_pow, h44]
          ring
  -- the constants
  have e1 : 2 * 16 ^ d * ‖SA‖ ^ 2 ≤ (2 ^ 20 * M ^ 2 / C) ^ d * Y :=
    calc 2 * 16 ^ d * ‖SA‖ ^ 2 ≤ 2 * 16 ^ d * ((β / C) ^ d * Y) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = 2 * 16 ^ d * β ^ d * Y / (C : ℝ) ^ d := by rw [div_pow]; ring
      _ ≤ (2 ^ 20 * M ^ 2) ^ d * Y / (C : ℝ) ^ d := by
          gcongr
          exact const_bound_one hβ hd
      _ = (2 ^ 20 * M ^ 2 / C) ^ d * Y := by rw [div_pow]; ring
  have e2 : 2 * (1 + 4 ^ d) ^ 2 * ‖A - B‖ ^ 2 ≤ (2 ^ 20 * M ^ 2) ^ d * R ^ (2 * d) * C * D :=
    calc 2 * (1 + 4 ^ d) ^ 2 * ‖A - B‖ ^ 2
        ≤ 2 * (1 + 4 ^ d) ^ 2 * (R ^ (2 * d) * (4 * ((2 * d : ℕ) : ℝ) ^ 4 * M ^ (2 * d) * C * D)) :=
          mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = (2 * (1 + 4 ^ d) ^ 2 * (4 * ((2 * d : ℕ) : ℝ) ^ 4 * M ^ (2 * d))) *
            (R ^ (2 * d) * C * D) := by ring
      _ ≤ (2 ^ 20 * M ^ 2) ^ d * (R ^ (2 * d) * C * D) :=
          mul_le_mul_of_nonneg_right (const_bound_two β hd) (by positivity)
      _ = (2 ^ 20 * M ^ 2) ^ d * R ^ (2 * d) * C * D := by ring
  have hfin : ‖A‖ ^ 2 ≤
      (2 ^ 20 * M ^ 2 / C) ^ d * Y + (2 ^ 20 * M ^ 2) ^ d * R ^ (2 * d) * C * D := by
    refine hsq.trans ?_
    rw [add_comm]
    exact add_le_add e1 e2
  exact hfin

end HeatModel

end FunctionalInequalities.KLS.LogConcave.PoissonIterate
