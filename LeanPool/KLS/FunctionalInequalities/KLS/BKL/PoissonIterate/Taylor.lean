/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.PoissonIterate.Domain
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.Tilt
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SpectralGap.Temperate

/-!
# Corollary 3.7 and Lemma 3.9 of BKL for the iterates in `D(A)`

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 3, (49), (52) (Corollary 3.7), (61) and
Lemma 3.9, for the iterates `iter Tbar f k` (the source's `h_{k+1}`) of `PoissonIterate/Basic.lean`
in the heat model `ν = m.tilted (-U)`, `U ∈ C²` with all exponential moments, `Tbar` the closed
unit-weight gradient, `A = Tbar†Tbar = -ℒ` and `C_P(ν) ≤ C`. Coefficient arrays are taken in
`stdOrthonormalBasis ℝ V`; `taylorField d u` puts the `d` Taylor indices first.

## What is proved

* `taylorTensor_gen_apply`: **Lemma 3.6 in coordinates**, for `u ∈ D(A)`:
  `T_{d+1}(A u)(e_{i₀}, …, e_{i_d})` is the average over `τ ∈ Perm (Fin (d + 1))` of
  `T_d(∂_{i_{τ d}} u)(e_{i_{τ 0}}, …, e_{i_{τ (d-1)}})`;
* `symmetrize_taylorField_grad0_step`, `symmetrize_taylorField_grad0_iter_succ`:
  **Corollary 3.7** (52), `S_{d+1} T_d(∇₀h_{k+2}) = α_{k+2} T_{d+1}(∇₀h_{k+1})` for `d ≥ 1`,
  entrywise with the index positions identified by `Fin.cast`;
* `meanGradSq_eq_norm_taylorField_one_genField`: **(49)** for fields in `D(A)`,
  `|∫ ∇h|² = |T₁(-L h)|²`; `meanGradSq_step`: **(61)**, `p_{k+2} = α_{k+2}² |T₁(∇₀h_{k+1})|²`;
* `sum_mean_partialDeriv_sq_le`, `meanGradSq_iter_zero_le`: the first energy drop
  `p₁ = |∫ ∇f|² ≤ ‖A f‖²` when `∫ ⟪v, x⟫² dν ≤ ‖v‖²` for all `v`;
* `sum_meanGradSq_iter_le`: **Lemma 3.9 in the form used here**, if `α_{j+2}² ≤ β/C` for
  `j + 1 < N` then `Σ_{k<N} p_{k+1} ≤ ‖L h₁‖² + (β/C) Σ_{k<N-1} |T₁(∇₀h_{k+1})|²`.

Generic facts on the way: `T_d` is homogeneous on `L²` classes (`taylorTensor_Lp_smul`,
`taylorField_smul`), does not see centering for `d ≥ 1` (`taylorTensor_center`), `T_0 u = ∫ u`
(`taylorTensor_zero_Lp`), pairing commutes with `T_d` (`innerSL_comp_taylorTensor_Lp`), and
`S_q` on a coordinate tensor is the full symmetrization of its slices with the trailing indices
fixed (`symmetrize_apply_comp_cast`).

## The argument

Lemma 3.6 on `D(A)` (`taylorTensor_adjointComp_eq`) gives `T_{d+1}(A u) = S_{d+1}(⟪T_d(Tbaru), ·⟫)`;
pairing `T_d(Tbaru)` with `e_j` is `T_d(∂_j u)`. For `h' = α (-L)⁻¹∇₀h` the components lie in
`D(A)` with `A h'_I = α ∇₀h_I` (30), and `∇₀h'_{(j, I)}` differs from `∂_j h'_I` by a constant,
which `T_d` ignores for `d ≥ 1`. The permutations of the first `d + 1` of the `d + (k + 2)`
index positions are the permutations of `Fin (d + 1)` extended by the identity, which turns
`S_{d+1}` on the big array into the symmetrization of Lemma 3.6. For `d = 0` the same identity
reads `T₁(A u)(e_j) = ∫ ∂_j u` (49), whence (61) by (30). For the first term, with
`w = ∫ ∇f`, the linear function `ℓ = ⟪w, ·⟫` lies in `D(Tbar)` with `Tbar ℓ = w`, so
`|w|² = ⟪Tbarf, Tbarℓ⟫ = ⟪A f, ℓ⟫ ≤ ‖A f‖ ‖ℓ‖ ≤ ‖A f‖ |w|`.

## What this is not

The covariance hypothesis is used only as `∫ ⟪v, x⟫² dν ≤ ‖v‖²`; the centering `∫ x dν = 0` is
not needed. Lemma 3.8, the bound of Lemma 3.9 by `R` and Theorem 3.1 are
not proved here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate

section Generic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : ProbabilityMeasure V}

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- `T_d` is homogeneous on `L²(ν)` classes. -/
theorem taylorTensor_Lp_smul (c : ℝ) (u : Lp ℝ 2 (ν : Measure V)) (d : ℕ) :
    taylorTensor (ν : Measure V) (⇑(c • u)) d = c • taylorTensor (ν : Measure V) (⇑u) d := by
  rw [taylorTensor_congr_ae _ (Lp.coeFn_smul c u) d]
  exact taylorTensor_const_mul _ c _ d

omit [FiniteDimensional ℝ V] in
private theorem isProbabilityMeasure_expTilt
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) (z : V) :
    IsProbabilityMeasure (expTilt (ν : Measure V) z) := by
  apply isProbabilityMeasure_tilted
  refine (hexp ‖z‖).mono'
    (Real.continuous_exp.comp (continuous_const.inner continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (real_inner_le_norm z x)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem iteratedFDeriv_sub_const' (F : V → ℝ) (c : ℝ) {d : ℕ} (hd : 1 ≤ d) :
    iteratedFDeriv ℝ d (fun x => F x - c) = iteratedFDeriv ℝ d F := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  funext x
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  simp only [fderiv_sub_const]

omit [FiniteDimensional ℝ V] in
/-- Taylor tensors of degree `d ≥ 1` do not see centering: `T_d(u - ∫u) = T_d u`. -/
theorem taylorTensor_center
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (u : Lp ℝ 2 (ν : Measure V)) {d : ℕ} (hd : 1 ≤ d) :
    taylorTensor (ν : Measure V) (⇑(L2.center ν u)) d = taylorTensor (ν : Measure V) (⇑u) d := by
  rw [taylorTensor_congr_ae _ (L2.center_coeFn ν u) d]
  have havg : tiltAverage (ν : Measure V) (fun x => u x - L2.mean ν u) =
      fun z => tiltAverage (ν : Measure V) (⇑u) z - L2.mean ν u := by
    funext z
    have := isProbabilityMeasure_expTilt hexp z
    simp only [tiltAverage]
    rw [integral_sub (integrable_expTilt_of_memLp _ hexp (Lp.memLp u) z) (integrable_const _),
      integral_const]
    simp
  unfold taylorTensor
  rw [havg, iteratedFDeriv_sub_const' _ _ hd]

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The Taylor tensor of degree `0` is the mean: `T_0 u = ∫ u dν`. -/
theorem taylorTensor_zero_Lp (u : Lp ℝ 2 (ν : Measure V)) (v : Fin 0 → V) :
    taylorTensor (ν : Measure V) (⇑u) 0 v = L2.mean ν u := by
  simp [taylorTensor, tiltAverage, expTilt, L2.mean_eq_integral]

/-- Pairing the vector Taylor tensor of `G ∈ L²(ν; V)` with `w` is the Taylor tensor of the scalar
class `⟪w, G⟫`. -/
theorem innerSL_comp_taylorTensor_Lp
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (G : Lp V 2 (ν : Measure V)) (w : V) (d : ℕ) :
    (innerSL ℝ w).compContinuousMultilinearMap (taylorTensor (ν : Measure V) (⇑G) d) =
      taylorTensor (ν : Measure V) (⇑((innerSL ℝ w).compLp G)) d := by
  rw [taylorTensor_congr_ae _ ((innerSL ℝ w).coeFn_compLp G) d]
  exact clm_comp_taylorTensor _ (integrable_expTilt_of_memLp _ hexp (Lp.memLp G))
    (contDiff_tiltAverage_Lp _ hexp G) (innerSL ℝ w) d

omit [BorelSpace V] in
/-- `taylorField d` is homogeneous. -/
theorem taylorField_smul (d : ℕ) {k : ℕ} (c : ℝ) (u : Field ν k) :
    taylorField d (c • u) = c • taylorField d u := by
  ext J
  simp only [taylorField, Pi.smul_apply, taylorTensor_Lp_smul, PiLp.toLp_apply, PiLp.smul_apply,
    smul_apply, smul_eq_mul]

end Generic

section Slots

/-- A permutation of the first `q` of `q + r` positions, extended by the identity. -/
private def extendPerm {q r : ℕ} (τ : Equiv.Perm (Fin q)) : Equiv.Perm (Fin (q + r)) :=
  finSumFinEquiv.permCongr (Equiv.Perm.sumCongr τ 1)

private theorem extendPerm_castAdd {q r : ℕ} (τ : Equiv.Perm (Fin q)) (i : Fin q) :
    extendPerm (r := r) τ (Fin.castAdd r i) = Fin.castAdd r (τ i) := by
  simp [extendPerm, Equiv.permCongr_apply]

private theorem extendPerm_natAdd {q r : ℕ} (τ : Equiv.Perm (Fin q)) (j : Fin r) :
    extendPerm τ (Fin.natAdd q j) = Fin.natAdd q j := by
  simp [extendPerm, Equiv.permCongr_apply]

/-- Sums over the permutations of the first `q` positions are sums over `Perm (Fin q)`. -/
private theorem sum_fixingOutside_slots {M : Type*} [AddCommMonoid M] {q r : ℕ}
    (g : Equiv.Perm (Fin (q + r)) → M) :
    ∑ σ ∈ fixingOutside (slots (q + r) 0 q), g σ = ∑ τ : Equiv.Perm (Fin q), g (extendPerm τ) := by
  classical
  symm
  refine Finset.sum_bij (fun τ _ => extendPerm τ) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro τ _
    simp only [fixingOutside, Finset.mem_filter, Finset.mem_univ, true_and]
    intro x hx
    induction x using Fin.addCases with
    | left i => exact absurd (by simp [slots]) hx
    | right j => exact extendPerm_natAdd τ j
  · intro τ₁ _ τ₂ _ h
    ext i
    have := congrArg (fun σ : Equiv.Perm (Fin (q + r)) => (σ (Fin.castAdd r i) : ℕ)) h
    simpa [extendPerm_castAdd] using this
  · intro σ hσ
    simp only [fixingOutside, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    have hlt : ∀ i : Fin q, (σ (Fin.castAdd r i) : ℕ) < q := by
      intro i
      by_contra hc
      have hy : σ (Fin.castAdd r i) ∉ slots (q + r) 0 q := by simp [slots, hc]
      have h1 := σ.injective (hσ _ hy)
      have h2 := congrArg Fin.val h1
      simp at h2
      omega
    let f : Fin q → Fin q := fun i => ⟨σ (Fin.castAdd r i), hlt i⟩
    have hf : Function.Injective f := by
      intro i j hij
      have h1 : σ (Fin.castAdd r i) = σ (Fin.castAdd r j) :=
        Fin.ext (by simpa [f] using congrArg Fin.val hij)
      exact Fin.castAdd_injective q r (σ.injective h1)
    refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), Finset.mem_univ _, ?_⟩
    ext x
    induction x using Fin.addCases with
    | left i => simp [extendPerm_castAdd, f]
    | right j =>
      rw [extendPerm_natAdd]
      exact congrArg Fin.val (hσ _ (by simp [slots])).symm

private theorem card_fixingOutside_slots {q r : ℕ} :
    (fixingOutside (slots (q + r) 0 q)).card = q.factorial := by
  rw [Finset.card_eq_sum_ones, sum_fixingOutside_slots (fun _ => 1)]
  simp [Fintype.card_perm]

/-- `S_q` of a coordinate tensor, read entrywise: the average over the permutations `τ` of the
first `q` indices of `J`, the last `r` indices kept. -/
theorem symmetrize_apply_comp_cast {n N q r : ℕ} (h : N = q + r) (A : Coord n N)
    (J : Fin (q + r) → Fin n) :
    symmetrize n N q A (J ∘ Fin.cast h) =
      (q.factorial : ℝ)⁻¹ * ∑ τ : Equiv.Perm (Fin q),
        A (Fin.append (J ∘ Fin.castAdd r ∘ τ) (J ∘ Fin.natAdd q) ∘ Fin.cast h) := by
  subst h
  simp only [symmetrize, blockAverage, slotRep, MonoidHom.coe_mk, OneHom.coe_mk,
    PiLp.smul_apply, smul_eq_mul, card_fixingOutside_slots]
  congr 1
  rw [WithLp.ofLp_sum, Finset.sum_apply, sum_fixingOutside_slots]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [slotPerm_apply]
  refine congrArg A.ofLp (funext fun x => ?_)
  induction x using Fin.addCases with
  | left i => simp [extendPerm_castAdd]
  | right j => simp [extendPerm_natAdd]

private theorem append_cast_natAdd {α : Type*} {d k : ℕ} (h : d + (k + 2) = d + 1 + (k + 1))
    (a : Fin (d + 1) → α) (I : Fin (k + 1) → α) :
    (fun p : Fin (k + 2) => Fin.append a I (Fin.cast h (Fin.natAdd d p))) =
      Fin.cons (a (Fin.last d)) I := by
  funext p
  induction p using Fin.cases with
  | zero =>
    rw [show Fin.cast h (Fin.natAdd d 0) = Fin.castAdd (k + 1) (Fin.last d) from Fin.ext (by simp),
      Fin.append_left, Fin.cons_zero]
  | succ p =>
    rw [show Fin.cast h (Fin.natAdd d p.succ) = Fin.natAdd (d + 1) p from
      Fin.ext (by simp; omega), Fin.append_right, Fin.cons_succ]

private theorem append_cast_castAdd {α : Type*} {d k : ℕ} (h : d + (k + 2) = d + 1 + (k + 1))
    (a : Fin (d + 1) → α) (I : Fin (k + 1) → α) (p : Fin d) :
    Fin.append a I (Fin.cast h (Fin.castAdd (k + 2) p)) = a (Fin.castSucc p) := by
  rw [show Fin.cast h (Fin.castAdd (k + 2) p) = Fin.castAdd (k + 1) (Fin.castSucc p) from
    Fin.ext (by simp), Fin.append_left]

end Slots

section HeatModel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))

local notation "Tbar" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

include hνU hU hexp in
/-- **BKL Lemma 3.6 in coordinates**: for `u ∈ D(A)`, the entry of `T_{d+1}(A u)` at the basis
vectors `e_{i_0}, …, e_{i_d}` is the average over the permutations `τ` of `d + 1` positions of the
entry of `T_d(∂_{i_{τ d}} u)` at `e_{i_{τ 0}}, …, e_{i_{τ (d-1)}}`. -/
theorem taylorTensor_gen_apply {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp Tbar).domain)
    (d : ℕ) (i : Fin (d + 1) → Fin (Module.finrank ℝ V)) :
    taylorTensor (ν : Measure V) (⇑(gen Tbar u)) (d + 1) (fun p => stdOrthonormalBasis ℝ V (i p)) =
      ((d + 1).factorial : ℝ)⁻¹ * ∑ τ : Equiv.Perm (Fin (d + 1)),
        taylorTensor (ν : Measure V) (⇑(partialDeriv Tbar (i (τ (Fin.last d))) u)) d
          (fun p => stdOrthonormalBasis ℝ V (i (τ (Fin.castSucc p)))) := by
  rw [gen_of_mem _ hu, taylorTensor_adjointComp_eq m hν hi hνU (hU.of_le (by norm_num)) hexp
    ⟨u, hu⟩ d]
  simp only [symmetrizeML, smul_apply, sum_apply, ContinuousMultilinearMap.domDomCongr_apply,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [partialDeriv, weakGrad_of_mem _ (mem_domain_of_mem_adjointComp_domain _ ⟨u, hu⟩),
    ← innerSL_comp_taylorTensor_Lp hexp]
  simp only [appendInner, ContinuousMultilinearMap.uncurryRight_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  exact real_inner_comm _ _

variable {C : NNReal} (hC : Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal))

include hνU hU hexp hC in
/-- **BKL Corollary 3.7 for one step**: for `d ≥ 1` and `h' = α (-L)⁻¹∇₀h`,
`S_{d+1} T_d(∇₀h') = α T_{d+1}(∇₀h)`, the index positions of the two coefficient arrays identified
by `Fin.cast`. -/
theorem symmetrize_taylorField_grad0_step {k : ℕ} (h : Field ν k) {d : ℕ} (hd : 1 ≤ d)
    (J : Fin (d + 1 + (k + 1)) → Fin (Module.finrank ℝ V)) :
    symmetrize (Module.finrank ℝ V) (d + (k + 2)) (d + 1)
        (taylorField d (grad0 Tbar (step Tbar h))) (J ∘ Fin.cast (by omega)) =
      scale Tbar h * taylorField (d + 1) (grad0 Tbar h) J := by
  rw [symmetrize_apply_comp_cast]
  set I : Fin (k + 1) → Fin (Module.finrank ℝ V) := J ∘ Fin.natAdd (d + 1)
  set i : Fin (d + 1) → Fin (Module.finrank ℝ V) := J ∘ Fin.castAdd (k + 1)
  have hgen : gen Tbar (step Tbar h I) = scale Tbar h • grad0 Tbar h I :=
    congrFun (genField_step m hν hi hνU hU hC h) I
  have hR : scale Tbar h * taylorField (d + 1) (grad0 Tbar h) J =
      taylorTensor (ν : Measure V) (⇑(gen Tbar (step Tbar h I))) (d + 1)
        (fun p => stdOrthonormalBasis ℝ V (i p)) := by
    rw [hgen, taylorTensor_Lp_smul]
    rfl
  rw [hR, taylorTensor_gen_apply m hν hi hνU hU hexp (step_mem_domain m hν hi hνU hU hC h I)]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [taylorField, PiLp.toLp_apply, Function.comp_apply]
  rw [append_cast_natAdd, grad0, gradField, Fin.cons_zero, Fin.tail_cons,
    taylorTensor_center hexp _ hd]
  simp only [append_cast_castAdd, Function.comp_apply]
  rfl

include hνU hU hexp hC in
/-- **BKL Corollary 3.7** (52) along the iterates: for `d ≥ 1`,
`S_{d+1} T_d(∇₀h_{k+2}) = α_{k+2} T_{d+1}(∇₀h_{k+1})`. -/
theorem symmetrize_taylorField_grad0_iter_succ (f : Lp ℝ 2 (ν : Measure V)) (k : ℕ) {d : ℕ}
    (hd : 1 ≤ d) (J : Fin (d + 1 + (k + 1)) → Fin (Module.finrank ℝ V)) :
    symmetrize (Module.finrank ℝ V) (d + (k + 2)) (d + 1)
        (taylorField d (grad0 Tbar (iter Tbar f (k + 1)))) (J ∘ Fin.cast (by omega)) =
      scale Tbar (iter Tbar f k) * taylorField (d + 1) (grad0 Tbar (iter Tbar f k)) J :=
  symmetrize_taylorField_grad0_step m hν hi hνU hU hexp hC _ hd J

include hνU hU hexp in
/-- **BKL (49)** for tensor fields in `D(A)`: `|∫ ∇h|² = |T₁(-L h)|²`, i.e. the squared means of the
components of `∇h` sum to the squared Hilbert–Schmidt norm of `T₁` of `-L h`. -/
theorem meanGradSq_eq_norm_taylorField_one_genField {k : ℕ} (h : Field ν k)
    (hh : ∀ I, h I ∈ (adjointComp Tbar).domain) :
    meanGradSq Tbar h = ‖taylorField 1 (genField Tbar h)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, meanGradSq]
  let e : (Fin (k + 1) → Fin (Module.finrank ℝ V)) ≃ (Fin (1 + k) → Fin (Module.finrank ℝ V)) :=
    (Fin.consEquiv fun _ => Fin (Module.finrank ℝ V)).symm.trans
      (((Equiv.funUnique (Fin 1) _).symm.prodCongr (Equiv.refl _)).trans (Fin.appendEquiv 1 k))
  refine Fintype.sum_equiv e _ _ fun K => ?_
  have h1 : (fun p : Fin k => e K (Fin.natAdd 1 p)) = Fin.tail K := by
    funext p
    simp [e, Fin.consEquiv]
  have h2 : (fun p : Fin 1 => stdOrthonormalBasis ℝ V (e K (Fin.castAdd k p))) =
      fun p => stdOrthonormalBasis ℝ V ((fun _ : Fin 1 => K 0) p) := by
    funext p
    simp [e, Fin.consEquiv]
  simp only [taylorField, PiLp.toLp_apply, genField, Real.norm_eq_abs, sq_abs]
  rw [h1, h2, taylorTensor_gen_apply m hν hi hνU hU hexp (hh _) 0]
  simp [taylorTensor_zero_Lp, gradField]

include hνU hU hexp hC in
/-- **BKL (61)** for one step: `|∫ ∇h'|² = α² |T₁(∇₀h)|²` for `h' = α (-L)⁻¹∇₀h`. -/
theorem meanGradSq_step {k : ℕ} (h : Field ν k) :
    meanGradSq Tbar (step Tbar h) = scale Tbar h ^ 2 * ‖taylorField 1 (grad0 Tbar h)‖ ^ 2 := by
  rw [meanGradSq_eq_norm_taylorField_one_genField m hν hi hνU hU hexp _
      (step_mem_domain m hν hi hνU hU hC h), genField_step m hν hi hνU hU hC, taylorField_smul,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

omit [SecondCountableTopology V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem gradient_inner_right' (w x : V) : gradient (fun y : V => ⟪w, y⟫) x = w := by
  have hd : fderiv ℝ (fun y : V => ⟪w, y⟫) x = InnerProductSpace.toDual ℝ V w := by
    change fderiv ℝ (⇑(innerSL ℝ w)) x = _
    rw [((innerSL ℝ w).hasFDerivAt (x := x)).fderiv]
    ext y
    simp
  simp only [gradient, hd, LinearIsometryEquiv.symm_apply_apply]

include hexp in
/-- **The first energy drop of BKL Lemma 3.9** on the generator domain: if
`∫ ⟪v, x⟫² dν ≤ ‖v‖²` for every `v` (`Cov ν ≤ Id` for a centered law), then for `u ∈ D(A)`,
`|∫ ∇u|² = Σ_j (∫ ∂_j u)² ≤ ‖A u‖²`. With `w = ∫ ∇u`, `|w|² = ⟪∇u, ∇⟪w, ·⟫⟫ = ⟪A u, ⟪w, ·⟫⟫`
and `‖⟪w, ·⟫‖ ≤ |w|`. -/
theorem sum_mean_partialDeriv_sq_le
    (hcov : ∀ v : V, ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure V) ≤ ‖v‖ ^ 2)
    {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp Tbar).domain) :
    ∑ j, L2.mean ν (partialDeriv Tbar j u) ^ 2 ≤ ‖gen Tbar u‖ ^ 2 := by
  set b := stdOrthonormalBasis ℝ V
  have huT : u ∈ (Tbar).domain := mem_domain_of_mem_adjointComp_domain _ ⟨u, hu⟩
  set G := (Tbar) ⟨u, huT⟩ with hG
  set w : V := ∫ x, G x ∂(ν : Measure V)
  have hGi : Integrable (⇑G) (ν : Measure V) := (Lp.memLp G).integrable (by norm_num)
  have hmean : ∀ j, L2.mean ν (partialDeriv Tbar j u) = ⟪b j, w⟫ := by
    intro j
    rw [L2.mean_eq_integral, partialDeriv, weakGrad_of_mem _ huT, ← integral_inner hGi]
    exact integral_congr_ae ((innerSL ℝ (b j)).coeFn_compLp _)
  have hsum : ∑ j, L2.mean ν (partialDeriv Tbar j u) ^ 2 = ‖w‖ ^ 2 := by
    simp_rw [hmean]
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner w w]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm w (b j), sq]
  obtain ⟨hℓ2, hg2, hmem, hT⟩ :=
    exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth m hν hi hexp
      (Function.hasTemperateGrowth_inner_right w)
  have hinner : ⟪gen Tbar u, hℓ2.toLp _⟫ = ‖w‖ ^ 2 := by
    rw [gen_of_mem _ hu, inner_adjointComp
      (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ⟨u, hu⟩ hmem, hT,
      MeasureTheory.L2.inner_def, ← real_inner_self_eq_norm_sq]
    calc ∫ x, ⟪G x, hg2.toLp (gradient fun y : V => ⟪w, y⟫) x⟫ ∂(ν : Measure V) =
          ∫ x, ⟪w, G x⟫ ∂(ν : Measure V) := by
          refine integral_congr_ae ?_
          filter_upwards [hg2.coeFn_toLp] with x hx
          rw [hx, gradient_inner_right', real_inner_comm]
      _ = ⟪w, w⟫ := integral_inner hGi w
  have hℓ : ‖hℓ2.toLp (fun y : V => ⟪w, y⟫)‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [L2.norm_toLp_sq]
    simpa only [Real.norm_eq_abs, sq_abs] using hcov w
  have hCS := real_inner_le_norm (gen Tbar u) (hℓ2.toLp (fun y : V => ⟪w, y⟫))
  rw [hinner] at hCS
  rw [hsum]
  have h0 : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  have h4 : (‖w‖ ^ 2) ^ 2 ≤ ‖gen Tbar u‖ ^ 2 * ‖w‖ ^ 2 := by
    calc (‖w‖ ^ 2) ^ 2 ≤ (‖gen Tbar u‖ * ‖hℓ2.toLp (fun y : V => ⟪w, y⟫)‖) ^ 2 :=
          pow_le_pow_left₀ h0 hCS 2
      _ = ‖gen Tbar u‖ ^ 2 * ‖hℓ2.toLp (fun y : V => ⟪w, y⟫)‖ ^ 2 := by ring
      _ ≤ ‖gen Tbar u‖ ^ 2 * ‖w‖ ^ 2 := by gcongr
  nlinarith [sq_nonneg (‖gen Tbar u‖)]

include hexp in
/-- The first term of BKL Lemma 3.9: `p₁ ≤ ‖L h₁‖²` for `h₁ = f ∈ D(A)` and `Cov ν ≤ Id`. -/
theorem meanGradSq_iter_zero_le
    (hcov : ∀ v : V, ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure V) ≤ ‖v‖ ^ 2)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp Tbar).domain) :
    meanGradSq Tbar (iter Tbar f 0) ≤ normSq (genField Tbar (iter Tbar f 0)) := by
  have h1 : meanGradSq Tbar (iter Tbar f 0) = ∑ j, L2.mean ν (partialDeriv Tbar j f) ^ 2 :=
    Fintype.sum_equiv (Equiv.funUnique (Fin 1) _) _ _ fun K => rfl
  have h2 : normSq (genField Tbar (iter Tbar f 0)) = ‖gen Tbar f‖ ^ 2 := by
    simp [normSq, genField, iter]
  rw [h1, h2]
  exact sum_mean_partialDeriv_sq_le m hν hi hexp hcov hf

include hνU hU hexp hC in
/-- **BKL Lemma 3.9 in the form used here**: if `∫ ⟪v, x⟫² dν ≤ ‖v‖²` for every `v` and
`α_{j+2}² ≤ β/C` for `j + 1 < N`, then
`Σ_{k<N} p_{k+1} ≤ ‖L h₁‖² + (β/C) Σ_{k<N-1} |T₁(∇₀h_{k+1})|²`. -/
theorem sum_meanGradSq_iter_le
    (hcov : ∀ v : V, ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure V) ≤ ‖v‖ ^ 2)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp Tbar).domain) {β : ℝ} (N : ℕ)
    (hβ : ∀ j, j + 1 < N → scale Tbar (iter Tbar f j) ^ 2 ≤ β / C) :
    ∑ k ∈ Finset.range N, meanGradSq Tbar (iter Tbar f k) ≤
      normSq (genField Tbar (iter Tbar f 0)) +
        β / C * ∑ k ∈ Finset.range (N - 1), ‖taylorField 1 (grad0 Tbar (iter Tbar f k))‖ ^ 2 := by
  cases N with
  | zero => simpa using normSq_nonneg _
  | succ M =>
    rw [Finset.sum_range_succ', Nat.add_sub_cancel, Finset.mul_sum, add_comm]
    refine add_le_add (meanGradSq_iter_zero_le m hν hi hexp hcov hf)
      (Finset.sum_le_sum fun k hk => ?_)
    rw [iter_succ, meanGradSq_step m hν hi hνU hU hexp hC]
    exact mul_le_mul_of_nonneg_right (hβ k (by simp at hk; omega)) (sq_nonneg _)

end HeatModel

end FunctionalInequalities.KLS.LogConcave.PoissonIterate
