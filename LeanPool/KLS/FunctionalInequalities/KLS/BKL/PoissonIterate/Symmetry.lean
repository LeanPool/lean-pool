/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.PoissonIterate.Defect
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.PoissonIterate.Permutation

/-!
# Approximate symmetry of the BKL iterates: Lemma 3.3

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Lemma 3.3, pp. 12–13, (41)–(44), for the iterates
`iter Tbar f k` of `PoissonIterate/Basic.lean` (the source's `h_{k+1}`) in the heat model
`ν = m.tilted (-U)`, with `Tbar` the closed unit-weight gradient, `A = Tbar†Tbar = -ℒ` and
`C_P(ν) ≤ C`. Write `H_k = ∇₀h_{k+1} = grad0 (iter k)` (a field with `k + 1` indices),
`α = scale (iter k)` (the source's `α_{k+2}`), `χ_k = defect (iter k)` and `τ_ℓ` for the
transposition of the index positions `ℓ` and `ℓ + 1` (`Equiv.swap ℓ (finRotate _ ℓ)`).

## What is proved

* `permField_grad0`: a permutation of the old index positions commutes with `∇₀`, which adds a
  new first position; `grad0_sub` (on `D(T)`) and `grad0_smul`: `∇₀` is linear;
* `normSq_grad0_invField_le`: BKL (20)/(24) for fields, `‖∇₀(-L)⁻¹g‖² ≤ C ‖g‖²` for centered
  components;
* `grad0_step_sub_permField_succ`: **(42)**, for `h' = α (-L)⁻¹ ∇₀h` and `ℓ + 1 < k + 1`:
  `∇₀h' - τ_{ℓ+1} ∇₀h' = α ∇₀(-L)⁻¹(∇₀h - τ_ℓ ∇₀h)`, and its norm form
  `normSq_grad0_step_sub_permField_succ_le` with the factor `α² C`;
* `normSq_grad0_iter_succ_sub_permField_swap_le`: from Lemma 3.2, `‖H_{k+1} - τ₀ H_{k+1}‖² ≤
  4 C χ_k`;
* `normSq_grad0_iter_sub_permField_le`: **(43)**, for `ℓ < k` and `α_j² ≤ β/C` for
  `k - ℓ ≤ j < k`: `‖H_k - τ_ℓ H_k‖² ≤ max(1, β)^ℓ · 4 C χ_{k-ℓ-1}`;
* `normSq_grad0_iter_sub_symField_le`: **Lemma 3.3**, for `2 ≤ q ≤ k + 1` and
  `0 < α_j² ≤ β/C` for `k + 1 - q ≤ j < k`:
  `‖H_k - S_q H_k‖² ≤ 4 q⁴ max(1, β)^q C Σ_{k+1-q ≤ j < k} χ_j`.

## The argument

`τ_{ℓ+1}` with `ℓ + 1 < k + 1` fixes the new first position of `∇₀h'` and acts as `τ_ℓ` on the
others, so `τ_{ℓ+1} ∇₀h' = ∇₀(τ_ℓ h')`. The components of `h'` lie in `D(A) ⊆ D(Tbar)`, where `∇₀`
is
linear, and `(-L)⁻¹` is linear on centered inputs and acts componentwise; this gives (42).
The norm bound is `‖∇₀u‖² ≤ ‖∇u‖²` (centering removes the squared means) and
`‖∇(-L)⁻¹g‖² = ⟪g, (-L)⁻¹g⟫ ≤ C ‖g‖²` (`norm_weakGrad_centeredInv_sq_le`). Iterating (42) `ℓ`
times with `α² C ≤ β` reduces `τ_ℓ` to `τ₀`, where Lemma 3.2 gives a field `S` symmetric under
`τ₀` with `‖H - S‖² ≤ C χ`, hence `‖H - τ₀ H‖ ≤ 2 ‖H - S‖`. Finally (44)
(`normSq_sub_symField_le`) sums over `ℓ + 1 < q`, and `ℓ ↦ k - ℓ - 1` matches the defects
with `k + 1 - q ≤ j < k`.

## What this is not

The constant is the source's up to the factor `4` from `τ₀` and with `max(1, β)` in place of
`β` (the operator `α ∇₀(-L)⁻¹` has norm at most `√β`). The positivity `0 < α_j` and the
centering of `f` are not used. These are statements about `L²` classes in the operator domain,
not about the source's class `𝒜`; Corollary 3.7, Lemmas 3.8–3.9 and Theorem 3.1 are not
proved here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate

/-! ### Adjacent transpositions after a new first position -/

section Positions

/-- `finRotate` commutes with `Fin.succ` below the last position. -/
private theorem finRotate_succ_eq {k : ℕ} (ℓ : Fin (k + 1)) (hℓ : ℓ.val + 1 < k + 1) :
    finRotate (k + 2) ℓ.succ = (finRotate (k + 1) ℓ).succ := by
  have h1 : ℓ.succ ≠ Fin.last (k + 1) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_last] at this
    omega
  have h2 : ℓ ≠ Fin.last k := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  ext
  rw [coe_finRotate_of_ne_last h1, Fin.val_succ, Fin.val_succ, coe_finRotate_of_ne_last h2]

/-- `τ_{ℓ+1}` fixes the first position. -/
private theorem swap_succ_apply_zero {k : ℕ} (ℓ : Fin (k + 1)) (hℓ : ℓ.val + 1 < k + 1) :
    Equiv.swap ℓ.succ (finRotate (k + 2) ℓ.succ) 0 = 0 := by
  rw [finRotate_succ_eq ℓ hℓ]
  exact Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _).symm (Fin.succ_ne_zero _).symm

/-- `τ_{ℓ+1}` acts as `τ_ℓ` on the shifted positions. -/
private theorem swap_succ_apply_succ {k : ℕ} (ℓ : Fin (k + 1)) (hℓ : ℓ.val + 1 < k + 1)
    (i : Fin (k + 1)) :
    Equiv.swap ℓ.succ (finRotate (k + 2) ℓ.succ) i.succ =
      (Equiv.swap ℓ (finRotate (k + 1) ℓ) i).succ := by
  rw [finRotate_succ_eq ℓ hℓ]
  exact (Fin.succ_injective _).swap_apply _ _ _

/-- `τ₀` is the transposition of the first two positions. -/
private theorem swap_zero_finRotate {k : ℕ} :
    Equiv.swap (0 : Fin (k + 2)) (finRotate (k + 2) 0) = Equiv.swap 0 1 := by
  rw [finRotate_apply_zero]

end Positions

/-! ### Linearity of `∇₀` and its commutation with permutations -/

section General

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] {ν : ProbabilityMeasure V}
  (T : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V))

/-- A permutation `σ'` of `k + 1` positions that fixes the first one and acts as `σ` on the
others commutes with `∇₀`: `σ' ∇₀u = ∇₀(σ u)`. -/
theorem permField_grad0 {k : ℕ} (σ : Equiv.Perm (Fin k)) (σ' : Equiv.Perm (Fin (k + 1)))
    (h0 : σ' 0 = 0) (hs : ∀ i, σ' i.succ = (σ i).succ) (u : Field ν k) :
    permField σ' (grad0 T u) = grad0 T (permField σ u) := by
  funext J
  have hJ0 : (J ∘ σ') 0 = J 0 := by simp [h0]
  have hJt : Fin.tail (J ∘ σ') = Fin.tail J ∘ σ := by
    funext i
    simp [Fin.tail, hs]
  simp only [permField, grad0, gradField, hJ0, hJt]

/-- `∇₀` is additive on fields with components in `D(T)`. -/
theorem grad0_sub {k : ℕ} {u v : Field ν k} (hu : ∀ I, u I ∈ T.domain)
    (hv : ∀ I, v I ∈ T.domain) : grad0 T (u - v) = grad0 T u - grad0 T v := by
  funext J
  have hw : weakGrad T (u (Fin.tail J) - v (Fin.tail J)) =
      weakGrad T (u (Fin.tail J)) - weakGrad T (v (Fin.tail J)) := by
    rw [weakGrad_of_mem T (T.domain.sub_mem (hu _) (hv _)), weakGrad_of_mem T (hu _),
      weakGrad_of_mem T (hv _)]
    exact LinearPMap.map_sub T ⟨_, hu _⟩ ⟨_, hv _⟩
  have hL : ∀ (L : V →L[ℝ] ℝ) (a b : Lp V 2 (ν : Measure V)),
      L.compLp (a - b) = L.compLp a - L.compLp b :=
    fun L a b => (L.compLpₗ 2 (ν : Measure V)).map_sub a b
  simp only [grad0, gradField, partialDeriv, Pi.sub_apply, hw, hL]
  rw [sub_eq_add_neg, L2.center_add, ← neg_one_smul ℝ, L2.center_smul, neg_one_smul,
    ← sub_eq_add_neg]

/-- `∇₀` is homogeneous. -/
theorem grad0_smul {k : ℕ} (c : ℝ) (u : Field ν k) : grad0 T (c • u) = c • grad0 T u := by
  funext J
  have hL : ∀ (L : V →L[ℝ] ℝ) (a : Lp V 2 (ν : Measure V)),
      L.compLp (c • a) = c • L.compLp a :=
    fun L a => (L.compLpₗ 2 (ν : Measure V)).map_smul c a
  simp only [grad0, gradField, partialDeriv, Pi.smul_apply, weakGrad_smul, hL, L2.center_smul]

/-- Centering the gradient only lowers the norm: `‖∇₀u‖² ≤ ‖∇u‖²`. -/
theorem normSq_grad0_le_energy {k : ℕ} (u : Field ν k) : normSq (grad0 T u) ≤ energy T u := by
  have h := energy_sub_normSq_grad0 T u
  have hp : 0 ≤ meanGradSq T u := sum_nonneg fun _ _ => sq_nonneg _
  linarith

end General

/-! ### The commutation (42) -/

section HeatModel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  {C : NNReal} (hC : Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal))

local notation "Tbar" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

include hνU hU hC in
/-- The centered inverse commutes with subtraction on centered inputs. -/
private theorem centeredInv_sub {g₁ g₂ : Lp ℝ 2 (ν : Measure V)} (hg₁ : L2.mean ν g₁ = 0)
    (hg₂ : L2.mean ν g₂ = 0) :
    centeredInv Tbar (g₁ - g₂) = centeredInv Tbar g₁ - centeredInv Tbar g₂ := by
  have hneg : L2.mean ν ((-1 : ℝ) • g₂) = 0 := by rw [L2.mean_smul, hg₂, mul_zero]
  rw [sub_eq_add_neg, ← neg_one_smul ℝ g₂, centeredInv_add m hν hi hνU hU hC hg₁ hneg,
    centeredInv_smul m hν hi hνU hU hC _ hg₂, neg_one_smul, ← sub_eq_add_neg]

include hνU hU hC in
/-- **BKL (20)/(24) for fields.** For a field `g` with centered components,
`‖∇₀(-L)⁻¹g‖² ≤ C ‖g‖²`. -/
theorem normSq_grad0_invField_le {k : ℕ} {g : Field ν k} (hg : ∀ I, L2.mean ν (g I) = 0) :
    normSq (grad0 Tbar (invField Tbar g)) ≤ (C : ℝ) * normSq g := by
  refine (normSq_grad0_le_energy _ _).trans ?_
  rw [energy_eq_sum, normSq, mul_sum]
  refine sum_le_sum fun I _ => ?_
  obtain ⟨h1, h2⟩ := norm_weakGrad_centeredInv_sq_le m hν hi hνU hU hC (hg I)
  rw [invField, h1]
  exact h2

include hνU hU hC in
/-- **BKL (42).** For `h' = α (-L)⁻¹ ∇₀h` (`α = scale h`) and `ℓ + 1 < k + 1`, the transposition
`τ_{ℓ+1}` of the positions `ℓ + 1, ℓ + 2` of `∇₀h'` is the transposition `τ_ℓ` of `∇₀h`:
`∇₀h' - τ_{ℓ+1} ∇₀h' = α ∇₀(-L)⁻¹(∇₀h - τ_ℓ ∇₀h)`. -/
theorem grad0_step_sub_permField_succ {k : ℕ} (h : Field ν k) (ℓ : Fin (k + 1))
    (hℓ : ℓ.val + 1 < k + 1) :
    grad0 Tbar (step Tbar h) -
        permField (Equiv.swap ℓ.succ (finRotate (k + 2) ℓ.succ)) (grad0 Tbar (step Tbar h)) =
      scale Tbar h • grad0 Tbar (invField Tbar
        (grad0 Tbar h - permField (Equiv.swap ℓ (finRotate (k + 1) ℓ)) (grad0 Tbar h))) := by
  set τ := Equiv.swap ℓ (finRotate (k + 1) ℓ)
  have hdom : ∀ J, step Tbar h J ∈ (Tbar).domain := fun J =>
    mem_domain_of_mem_adjointComp_domain _ ⟨_, step_mem_domain m hν hi hνU hU hC h J⟩
  rw [permField_grad0 _ τ _ (swap_succ_apply_zero ℓ hℓ) (swap_succ_apply_succ ℓ hℓ),
    ← grad0_sub _ (v := permField τ (step Tbar h)) hdom (fun J => hdom _)]
  have e : step Tbar h - permField τ (step Tbar h) =
      scale Tbar h • invField Tbar (grad0 Tbar h - permField τ (grad0 Tbar h)) := by
    funext I
    simp only [step, Pi.sub_apply, Pi.smul_apply, permField, invField]
    rw [centeredInv_sub m hν hi hνU hU hC (mean_grad0 _ h _) (mean_grad0 _ h _), smul_sub]
  rw [e, grad0_smul]

include hνU hU hC in
/-- **BKL (42), norm form.** `‖∇₀h' - τ_{ℓ+1} ∇₀h'‖² ≤ α² C ‖∇₀h - τ_ℓ ∇₀h‖²`. -/
theorem normSq_grad0_step_sub_permField_succ_le {k : ℕ} (h : Field ν k) (ℓ : Fin (k + 1))
    (hℓ : ℓ.val + 1 < k + 1) :
    normSq (grad0 Tbar (step Tbar h) -
        permField (Equiv.swap ℓ.succ (finRotate (k + 2) ℓ.succ)) (grad0 Tbar (step Tbar h))) ≤
      scale Tbar h ^ 2 * (C : ℝ) *
        normSq (grad0 Tbar h - permField (Equiv.swap ℓ (finRotate (k + 1) ℓ)) (grad0 Tbar h)) := by
  rw [grad0_step_sub_permField_succ m hν hi hνU hU hC h ℓ hℓ, normSq_smul, mul_assoc]
  refine mul_le_mul_of_nonneg_left (normSq_grad0_invField_le m hν hi hνU hU hC fun I => ?_)
    (sq_nonneg _)
  simp only [Pi.sub_apply, permField, L2.mean_sub, mean_grad0, sub_zero]

end HeatModel

/-! ### Iterating (42): the bound (43) and Lemma 3.3 -/

section Iterates

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
  {C : NNReal} (hC : Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal))

local notation "Tbar" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

omit [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- If `σ` fixes `S`, then `‖u - σ u‖² ≤ 4 ‖u - S‖²`. -/
private theorem normSq_sub_permField_le_of_fixed {k : ℕ} (σ : Equiv.Perm (Fin k))
    {S : Field ν k} (hS : permField σ S = S) (u : Field ν k) :
    normSq (u - permField σ u) ≤ 4 * normSq (u - S) := by
  have e : u - permField σ u = (u - S) + -permField σ (u - S) := by
    rw [permField_sub, hS]
    abel
  have h : √(normSq (u - permField σ u)) ≤ 2 * √(normSq (u - S)) := by
    rw [e]
    refine (sqrt_normSq_add_le _ _).trans ?_
    rw [normSq_neg, normSq_permField]
    linarith
  have h' := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt (normSq_nonneg _), mul_pow, Real.sq_sqrt (normSq_nonneg _)] at h'
  norm_num at h'
  linarith

include hνU hUt hexp hC in
/-- **The first transposition**, from Lemma 3.2: `‖∇₀h_{k+2} - τ₀ ∇₀h_{k+2}‖² ≤ 4 C χ_{k+1}`. -/
theorem normSq_grad0_iter_succ_sub_permField_swap_le (hCpos : 0 < C)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp Tbar).domain) (k : ℕ) :
    normSq (grad0 Tbar (iter Tbar f (k + 1)) -
        permField (Equiv.swap 0 1) (grad0 Tbar (iter Tbar f (k + 1)))) ≤
      4 * (C : ℝ) * defect Tbar (iter Tbar f k) := by
  obtain ⟨S, hS, hle⟩ :=
    exists_symm_normSq_grad0_iter_succ_sub_le m hν hi hνU hUt hexp hC hCpos hf k
  refine (normSq_sub_permField_le_of_fixed _ (funext hS) _).trans ?_
  linarith

include hνU hUt hexp hC in
/-- The induction behind (43), by the number `n` of applications of (42). -/
private theorem normSq_grad0_iter_sub_permField_le_aux (hCpos : 0 < C)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp Tbar).domain) {β : ℝ} (n : ℕ) :
    ∀ (k : ℕ) (ℓ : Fin (k + 1)), ℓ.val = n → n < k →
      (∀ j, k - n ≤ j → j < k → scale Tbar (iter Tbar f j) ^ 2 ≤ β / C) →
      normSq (grad0 Tbar (iter Tbar f k) -
          permField (Equiv.swap ℓ (finRotate (k + 1) ℓ)) (grad0 Tbar (iter Tbar f k))) ≤
        max 1 β ^ n * (4 * (C : ℝ) * defect Tbar (iter Tbar f (k - n - 1))) := by
  have hU : ContDiff ℝ 2 U := hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hC0 : (0 : ℝ) < C := NNReal.coe_pos.mpr hCpos
  induction n with
  | zero =>
    intro k ℓ hℓ hk _
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain rfl : ℓ = 0 := Fin.ext hℓ
    rw [swap_zero_finRotate, pow_zero, one_mul, show k' + 1 - 0 - 1 = k' by omega]
    exact normSq_grad0_iter_succ_sub_permField_swap_le m hν hi hνU hUt hexp hC hCpos hf k'
  | succ n ih =>
    intro k ℓ hℓ hk hα
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨ℓ₀, rfl⟩ : ∃ ℓ₀ : Fin (k' + 1), ℓ₀.succ = ℓ :=
      Fin.exists_succ_eq.mpr fun h => by simp [h] at hℓ
    have hℓ₀ : ℓ₀.val = n := by simpa using hℓ
    have hstep := normSq_grad0_step_sub_permField_succ_le m hν hi hνU hU hC (iter Tbar f k') ℓ₀
      (by omega)
    have hIH := ih k' ℓ₀ hℓ₀ (by omega) fun j hj hj' => hα j (by omega) (by omega)
    have hαk : scale Tbar (iter Tbar f k') ^ 2 * (C : ℝ) ≤ max 1 β :=
      ((le_div_iff₀ hC0).mp (hα k' (by omega) (by omega))).trans (le_max_right _ _)
    rw [show k' + 1 - (n + 1) - 1 = k' - n - 1 by omega, pow_succ', mul_assoc]
    refine hstep.trans ?_
    exact mul_le_mul hαk hIH (normSq_nonneg _) (zero_le_one.trans (le_max_left _ _))

include hνU hUt hexp hC in
/-- **BKL (43).** For `ℓ < k` and `α_j² ≤ β/C` for `k - ℓ ≤ j < k`:
`‖∇₀h_{k+1} - τ_ℓ ∇₀h_{k+1}‖² ≤ max(1, β)^ℓ · 4 C χ_{k-ℓ}` (the defect of `iter (k - ℓ - 1)`). -/
theorem normSq_grad0_iter_sub_permField_le (hCpos : 0 < C)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp Tbar).domain) {β : ℝ} {k : ℕ}
    (ℓ : Fin (k + 1)) (hℓ : ℓ.val < k)
    (hα : ∀ j, k - ℓ.val ≤ j → j < k → scale Tbar (iter Tbar f j) ^ 2 ≤ β / C) :
    normSq (grad0 Tbar (iter Tbar f k) -
        permField (Equiv.swap ℓ (finRotate (k + 1) ℓ)) (grad0 Tbar (iter Tbar f k))) ≤
      max 1 β ^ ℓ.val * (4 * (C : ℝ) * defect Tbar (iter Tbar f (k - ℓ.val - 1))) :=
  normSq_grad0_iter_sub_permField_le_aux m hν hi hνU hUt hexp hC hCpos hf ℓ.val k ℓ rfl hℓ hα

/-- Reindexing the defects: `Σ_{ℓ+1<q} F (k - ℓ - 1) = Σ_{k+1-q ≤ j < k} F j`. -/
private theorem sum_filter_eq_sum_Ico {k q : ℕ} (hq : q ≤ k + 1) (F : ℕ → ℝ) :
    ∑ ℓ ∈ univ.filter (fun ℓ : Fin (k + 1) => ℓ.val + 1 < q), F (k - ℓ.val - 1) =
      ∑ j ∈ Ico (k + 1 - q) k, F j := by
  refine sum_bij' (fun ℓ _ => k - ℓ.val - 1) (fun j _ => ⟨k - 1 - j, by omega⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro ℓ hℓ
    simp only [mem_filter, mem_univ, true_and] at hℓ
    simp only [mem_Ico]
    omega
  · intro j hj
    simp only [mem_Ico] at hj
    simp only [mem_filter, mem_univ, true_and]
    omega
  · intro ℓ hℓ
    simp only [mem_filter, mem_univ, true_and] at hℓ
    ext
    simp only
    omega
  · intro j hj
    simp only [mem_Ico] at hj
    simp only
    omega
  · intro ℓ _
    rfl

include hνU hUt hexp hC in
/-- **BKL Lemma 3.3**, for every `q` with `2 ≤ q ≤ k + 1`, under `0 < α_j² ≤ β/C` for
`k + 1 - q ≤ j < k`: `∇₀h_{k+1}` is close to its symmetrization `S_q` over the first `q` index
positions, `‖∇₀h_{k+1} - S_q ∇₀h_{k+1}‖² ≤ 4 q⁴ max(1, β)^q C Σ_{k+1-q ≤ j < k} χ_j`. -/
theorem normSq_grad0_iter_sub_symField_le (hCpos : 0 < C)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp Tbar).domain) {β : ℝ} (k q : ℕ)
    (hq : 2 ≤ q) (hqk : q ≤ k + 1)
    (hα : ∀ j, k + 1 - q ≤ j → j < k →
      0 < scale Tbar (iter Tbar f j) ∧ scale Tbar (iter Tbar f j) ^ 2 ≤ β / C) :
    normSq (grad0 Tbar (iter Tbar f k) - symField q (grad0 Tbar (iter Tbar f k))) ≤
      4 * (q : ℝ) ^ 4 * max 1 β ^ q * C *
        ∑ j ∈ Finset.Ico (k + 1 - q) k, defect Tbar (iter Tbar f j) := by
  have hC0 : (0 : ℝ) ≤ C := C.2
  have hmax : (1 : ℝ) ≤ max 1 β := le_max_left _ _
  refine (normSq_sub_symField_le hqk _).trans ?_
  rw [← sum_filter_eq_sum_Ico hqk, mul_sum, mul_sum]
  refine sum_le_sum fun ℓ hℓ => ?_
  simp only [mem_filter, mem_univ, true_and] at hℓ
  have h := normSq_grad0_iter_sub_permField_le m hν hi hνU hUt hexp hC hCpos hf ℓ (by omega)
    fun j hj hj' => (hα j (by omega) hj').2
  have hpow : max 1 β ^ ℓ.val ≤ max 1 β ^ q := pow_le_pow_right₀ hmax (by omega)
  have hdef : 0 ≤ defect Tbar (iter Tbar f (k - ℓ.val - 1)) := normSq_nonneg _
  have hq4 : (0 : ℝ) ≤ (q : ℝ) ^ 4 := by positivity
  calc (q : ℝ) ^ 4 * normSq (grad0 Tbar (iter Tbar f k) -
        permField (Equiv.swap ℓ (finRotate (k + 1) ℓ)) (grad0 Tbar (iter Tbar f k)))
      ≤ (q : ℝ) ^ 4 * (max 1 β ^ q * (4 * (C : ℝ) * defect Tbar (iter Tbar f (k - ℓ.val - 1)))) :=
        mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right hpow (by positivity)))
          hq4
    _ = 4 * (q : ℝ) ^ 4 * max 1 β ^ q * C * defect Tbar (iter Tbar f (k - ℓ.val - 1)) := by ring

end Iterates

end FunctionalInequalities.KLS.LogConcave.PoissonIterate
