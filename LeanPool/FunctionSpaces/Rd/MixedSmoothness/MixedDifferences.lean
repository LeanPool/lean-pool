/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.MixedSmoothness.TensorKernels
public import LeanPool.FunctionSpaces.Rd.MixedSmoothness.MixedSequences
public import LeanPool.FunctionSpaces.Rd.Differences.DilatedDifferences
public import LeanPool.FunctionSpaces.Analysis.Differences.TranslationAlgebra

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Mixed differences and mixed moduli of smoothness on `ℝ^d`

On `ℝ^d = Fin d → ℝ`, the **mixed difference** of order `L` in the coordinates of `e ⊆ {0, …, d-1}`
with steps `h_i` is

`Δ^{L,e}_h f = (∏_{i ∈ e} Δ^L_{h_i e_i}) f`

(`Rd.mixedDiff`), the action of `∏_{i ∈ e} (δ_{h_i e_i} - 1)^L` in the commutative algebra of
translations (`TranslationAlgebra.diffAct`), so the order of the coordinates does not matter. Adding
a coordinate applies one more difference (`Rd.mixedDiff_insert`). Mixed differences are linear, keep
measurability and integrability, satisfy `‖Δ^{L,e}_h f‖_p ≤ 2^(L|e|) ‖f‖_p`, act on each factor of a
tensor kernel (`Rd.mixedDiff_tensorKernel`) and move from a convolution onto its kernel,
`Δ^{L,e}_h (K ⋆ f) = (Δ^{L,e}_h K) ⋆ f` almost everywhere (`Rd.mixedDiff_conv_ae`).

The **mixed modulus of smoothness** is `Ω^e_L(f, t)_p = sup_{|h_i| ≤ t_i, i ∈ e} ‖Δ^{L,e}_h f‖_p`
(`Rd.mixedModulus`; T. Ullrich), and for `f ∈ L_p` and `k ∈ ℕ^d` we use it in the coordinates
`e(k) = {i : k_i ≠ 0}` at the dyadic scale `2^(-k)`, `Ω^{e(k)}_L(f, 2^(-k))_p`
(`Rd.lpMixedModulus`); `k = 0` gives `‖f‖_p`. The **Besov quasi-norm of dominating mixed
smoothness by differences** is

`‖(2^(s|k|_1) Ω^{e(k)}_L(f, 2^(-k))_p)_{k ∈ ℕ^d}‖_{ℓ_q(ℕ^d)}`

(`Rd.mixedModNorm`), with one `ℓ_q` norm over `ℕ^d`, matching the indexing of the mixed local
means.
-/

@[expose] public section

open MeasureTheory Filter
open TranslationAlgebra (coordElem diffAct higherDiff_eq_diffAct)
open scoped ENNReal

open ENNReal (dyadicWeight lqNorm)

namespace Rd

variable {d : ℕ}

/-! ### Mixed differences -/

/-- The **mixed difference** `Δ^{L,e}_h f = (∏_{i ∈ e} Δ^L_{h_i e_i}) f`, the action of
`∏_{i ∈ e} (δ_{h_i e_i} - 1)^L` in the algebra of translations. -/
noncomputable def mixedDiff (L : ℕ) (e : Finset (Fin d)) (h : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℂ) : (Fin d → ℝ) → ℂ :=
  diffAct (∏ i ∈ e, coordElem h i ^ L) f

/-- `(δ_{h_i e_i} - 1)^L` acts by the difference `Δ^L_{h_i e_i}`. -/
theorem diffAct_coordElem_pow_eq_higherDiff (L : ℕ) (h : Fin d → ℝ) (i : Fin d)
    (f : (Fin d → ℝ) → ℂ) :
    diffAct (coordElem h i ^ L) f = (fwdDiff (Pi.single i (h i)))^[L] f := by
  rw [coordElem, ← higherDiff_eq_diffAct]
  rfl

/-- The mixed difference in no coordinate is the function itself. -/
theorem mixedDiff_empty (L : ℕ) (h : Fin d → ℝ) (f : (Fin d → ℝ) → ℂ) :
    mixedDiff L ∅ h f = f := by
  simp [mixedDiff]

/-- **Adding a coordinate**: `Δ^{L, e ∪ {i}}_h = Δ^L_{h_i e_i} Δ^{L,e}_h` for `i ∉ e`. -/
theorem mixedDiff_insert (L : ℕ) {e : Finset (Fin d)} {i : Fin d} (hi : i ∉ e) (h : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℂ) :
    mixedDiff L (insert i e) h f = (fwdDiff (Pi.single i (h i)))^[L] (mixedDiff L e h f) := by
  rw [mixedDiff, Finset.prod_insert hi, map_mul, mul_apply_eq_comp,
    diffAct_coordElem_pow_eq_higherDiff]
  rfl

/-- Mixed differences are additive. -/
theorem mixedDiff_add (L : ℕ) (e : Finset (Fin d)) (h : Fin d → ℝ) (f g : (Fin d → ℝ) → ℂ) :
    mixedDiff L e h (f + g) = mixedDiff L e h f + mixedDiff L e h g :=
  map_add _ f g

/-- Mixed differences are subtractive. -/
theorem mixedDiff_sub (L : ℕ) (e : Finset (Fin d)) (h : Fin d → ℝ) (f g : (Fin d → ℝ) → ℂ) :
    mixedDiff L e h (f - g) = mixedDiff L e h f - mixedDiff L e h g :=
  map_sub _ f g

/-- Mixed differences of a.e. strongly measurable functions are a.e. strongly measurable. -/
theorem aestronglyMeasurable_mixedDiff {f : (Fin d → ℝ) → ℂ} (hf : AEStronglyMeasurable f volume)
    (L : ℕ) (e : Finset (Fin d)) (h : Fin d → ℝ) :
    AEStronglyMeasurable (mixedDiff L e h f) volume := by
  induction e using Finset.induction_on with
  | empty => rwa [mixedDiff_empty]
  | insert i e hi ih =>
    rw [mixedDiff_insert L hi]
    exact aestronglyMeasurable_higherDiff ih L _

/-- Mixed differences of integrable functions are integrable. -/
theorem integrable_mixedDiff {K : (Fin d → ℝ) → ℂ} (hK : Integrable K) (L : ℕ)
    (e : Finset (Fin d)) (h : Fin d → ℝ) : Integrable (mixedDiff L e h K) := by
  induction e using Finset.induction_on with
  | empty => rwa [mixedDiff_empty]
  | insert i e hi ih =>
    rw [mixedDiff_insert L hi]
    exact integrable_higherDiff ih L _

/-- **Mixed differences depend only on the class modulo null sets.** -/
theorem mixedDiff_congr_ae {f g : (Fin d → ℝ) → ℂ} (hfg : f =ᵐ[volume] g) (L : ℕ)
    (e : Finset (Fin d)) (h : Fin d → ℝ) :
    mixedDiff L e h f =ᵐ[volume] mixedDiff L e h g := by
  induction e using Finset.induction_on with
  | empty => rwa [mixedDiff_empty, mixedDiff_empty]
  | insert i e hi ih =>
    rw [mixedDiff_insert L hi, mixedDiff_insert L hi]
    exact higherDiff_congr_ae ih L _

/-- `‖Δ^{L,e}_h f‖_p ≤ 2^(L|e|) ‖f‖_p`. -/
theorem eLpNorm_mixedDiff_le {f : (Fin d → ℝ) → ℂ} (hf : AEStronglyMeasurable f volume)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (L : ℕ) (e : Finset (Fin d)) (h : Fin d → ℝ) :
    eLpNorm (mixedDiff L e h f) p volume ≤ 2 ^ (L * e.card) * eLpNorm f p volume := by
  induction e using Finset.induction_on with
  | empty => simp [mixedDiff_empty]
  | insert i e hi ih =>
    rw [mixedDiff_insert L hi, Finset.card_insert_of_notMem hi]
    calc eLpNorm ((fwdDiff (Pi.single i (h i)))^[L] (mixedDiff L e h f)) p volume
        ≤ 2 ^ L * eLpNorm (mixedDiff L e h f) p volume :=
          eLpNorm_higherDiff_le (aestronglyMeasurable_mixedDiff hf L e h) hp L _
      _ ≤ 2 ^ L * (2 ^ (L * e.card) * eLpNorm f p volume) := mul_le_mul' le_rfl ih
      _ = 2 ^ (L * (e.card + 1)) * eLpNorm f p volume := by
          rw [← mul_assoc, ← pow_add]
          ring_nf

/-- **Mixed differences of convolutions** fall on the kernel:
`Δ^{L,e}_h (K ⋆ f) = (Δ^{L,e}_h K) ⋆ f` almost everywhere, for integrable `K` and `f ∈ L_p`. -/
theorem mixedDiff_conv_ae {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K f : (Fin d → ℝ) → ℂ}
    (hK : Integrable K) (hf : MemLp f p volume) (L : ℕ) (e : Finset (Fin d)) (h : Fin d → ℝ) :
    mixedDiff L e h (conv K f volume) =ᵐ[volume] conv (mixedDiff L e h K) f volume := by
  induction e using Finset.induction_on with
  | empty => rw [mixedDiff_empty, mixedDiff_empty]
  | insert i e hi ih =>
    rw [mixedDiff_insert L hi, mixedDiff_insert L hi]
    exact (higherDiff_congr_ae ih L _).trans
      (higherDiff_conv_ae hp1 hp (integrable_mixedDiff hK L e h) hf L _)

/-! ### Mixed differences of tensor kernels -/

/-- **A difference in coordinate `i` of a tensor product** acts on the `i`-th factor:
`Δ_{t e_i} (⊗K) = ⊗K'` with `K'_i = Δ_t K_i` and `K'_j = K_j` otherwise. -/
theorem fwdDiff_single_tensorKernel (K : Fin d → ℝ → ℂ) (i : Fin d) (t : ℝ) :
    fwdDiff (Pi.single i t) (tensorKernel K) =
      tensorKernel (Function.update K i (fwdDiff t (K i))) := by
  funext x
  simp only [fwdDiff, tensorKernel]
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i (fun j => K j (x j)),
    Fintype.prod_eq_mul_prod_compl i (fun j => Function.update K i (fwdDiff t (K i)) j (x j))]
  have h1 : ∏ j ∈ {i}ᶜ, K j ((x + Pi.single i t : Fin d → ℝ) j) = ∏ j ∈ {i}ᶜ, K j (x j) :=
    Finset.prod_congr rfl fun j hj => by
      have hji : j ≠ i := by simpa using hj
      simp [hji]
  have h2 : ∏ j ∈ {i}ᶜ, Function.update K i (fwdDiff t (K i)) j (x j) =
      ∏ j ∈ {i}ᶜ, K j (x j) :=
    Finset.prod_congr rfl fun j hj => by
      have hji : j ≠ i := by simpa using hj
      simp [hji]
  rw [h1, h2]
  simp only [Pi.add_apply, Pi.single_eq_same, Function.update_self, fwdDiff]
  ring

/-- **Differences of order `L` in coordinate `i` of a tensor product** act on the `i`-th
factor. -/
theorem higherDiff_single_tensorKernel (L : ℕ) (K : Fin d → ℝ → ℂ) (i : Fin d) (t : ℝ) :
    (fwdDiff (Pi.single i t))^[L] (tensorKernel K) =
      tensorKernel (Function.update K i ((fwdDiff t)^[L] (K i))) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Function.iterate_succ_apply', ih, fwdDiff_single_tensorKernel, Function.update_idem,
      Function.update_self, Function.iterate_succ_apply']

/-- **Mixed differences of tensor products** act on the factors of the coordinates in `e`:
`Δ^{L,e}_h (⊗K) = ⊗K'` with `K'_i = Δ^L_{h_i} K_i` for `i ∈ e` and `K'_i = K_i` otherwise. -/
theorem mixedDiff_tensorKernel (L : ℕ) (e : Finset (Fin d)) (h : Fin d → ℝ)
    (K : Fin d → ℝ → ℂ) :
    mixedDiff L e h (tensorKernel K) =
      tensorKernel fun i => if i ∈ e then (fwdDiff (h i))^[L] (K i) else K i := by
  induction e using Finset.induction_on with
  | empty => simp [mixedDiff_empty]
  | insert i e hi ih =>
    rw [mixedDiff_insert L hi, ih, higherDiff_single_tensorKernel]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp [hi]
    · simp [Finset.mem_insert, hj]

/-! ### Mixed moduli of smoothness -/

/-- The **mixed modulus of smoothness** `Ω^e_L(f, t)_p = sup ‖Δ^{L,e}_h f‖_p` over the steps with
`|h_i| ≤ t_i` for `i ∈ e`. -/
noncomputable def mixedModulus (L : ℕ) (e : Finset (Fin d)) (p : ℝ≥0∞) (f : (Fin d → ℝ) → ℂ)
    (t : Fin d → ℝ) : ℝ≥0∞ :=
  ⨆ (h : Fin d → ℝ) (_ : ∀ i ∈ e, |h i| ≤ t i), eLpNorm (mixedDiff L e h f) p volume

/-- Each admissible step is bounded by the mixed modulus. -/
theorem eLpNorm_mixedDiff_le_mixedModulus {L : ℕ} {e : Finset (Fin d)} {p : ℝ≥0∞}
    {f : (Fin d → ℝ) → ℂ} {t h : Fin d → ℝ} (hh : ∀ i ∈ e, |h i| ≤ t i) :
    eLpNorm (mixedDiff L e h f) p volume ≤ mixedModulus L e p f t :=
  le_iSup₂ (f := fun (h : Fin d → ℝ) (_ : ∀ i ∈ e, |h i| ≤ t i) =>
    eLpNorm (mixedDiff L e h f) p volume) h hh

/-- The mixed modulus increases in `t`. -/
theorem mixedModulus_mono (L : ℕ) (e : Finset (Fin d)) (p : ℝ≥0∞) (f : (Fin d → ℝ) → ℂ)
    {t t' : Fin d → ℝ} (htt' : ∀ i ∈ e, t i ≤ t' i) :
    mixedModulus L e p f t ≤ mixedModulus L e p f t' :=
  iSup₂_le fun _ hh => eLpNorm_mixedDiff_le_mixedModulus fun i hi => (hh i hi).trans (htt' i hi)

/-- The mixed modulus in no coordinate is the norm. -/
theorem mixedModulus_empty (L : ℕ) (p : ℝ≥0∞) (f : (Fin d → ℝ) → ℂ) (t : Fin d → ℝ) :
    mixedModulus L ∅ p f t = eLpNorm f p volume := by
  simp [mixedModulus, mixedDiff_empty]

/-- The mixed modulus is subadditive. -/
theorem mixedModulus_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) (L : ℕ) (e : Finset (Fin d))
    (f g : (Fin d → ℝ) → ℂ) (t : Fin d → ℝ) :
    mixedModulus L e p (f + g) t ≤ mixedModulus L e p f t + mixedModulus L e p g t := by
  refine iSup₂_le fun h hh => ?_
  rw [mixedDiff_add]
  exact (eLpNorm_add_le hp).trans
      (add_le_add (eLpNorm_mixedDiff_le_mixedModulus hh) (eLpNorm_mixedDiff_le_mixedModulus hh))

/-- `Ω^e_L(f, t)_p ≤ 2^(L|e|) ‖f‖_p`. -/
theorem mixedModulus_le {f : (Fin d → ℝ) → ℂ} (hf : AEStronglyMeasurable f volume) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (L : ℕ) (e : Finset (Fin d)) (t : Fin d → ℝ) :
    mixedModulus L e p f t ≤ 2 ^ (L * e.card) * eLpNorm f p volume :=
  iSup₂_le fun h _ => eLpNorm_mixedDiff_le hf hp L e h

/-- **The mixed modulus depends only on the class modulo null sets.** -/
theorem mixedModulus_congr_ae {f g : (Fin d → ℝ) → ℂ} (hfg : f =ᵐ[volume] g) (L : ℕ)
    (e : Finset (Fin d)) (p : ℝ≥0∞) (t : Fin d → ℝ) :
    mixedModulus L e p f t = mixedModulus L e p g t := by
  simp only [mixedModulus]
  congr 1
  funext h
  congr 1
  funext _
  exact eLpNorm_congr_ae (mixedDiff_congr_ae hfg L e h)

/-! ### The mixed modulus on `L_p` at dyadic scales -/

/-- The coordinates `e(k) = {i : k_i ≠ 0}` in which the index `k ∈ ℕ^d` takes differences. -/
def mixedSupp (k : Fin d → ℕ) : Finset (Fin d) := Finset.univ.filter fun i => k i ≠ 0

/-- The index `0` takes no differences. -/
theorem mixedSupp_zero : mixedSupp (0 : Fin d → ℕ) = ∅ := by
  simp [mixedSupp]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The **mixed modulus at the dyadic scale `2^(-k)`** of `f ∈ L_p`,
`Ω^{e(k)}_L(f, 2^(-k))_p` with `e(k) = {i : k_i ≠ 0}`. -/
noncomputable def lpMixedModulus (L : ℕ) (f : Lp ℂ p (volume : Measure (Fin d → ℝ)))
    (k : Fin d → ℕ) : ℝ≥0∞ :=
  mixedModulus L (mixedSupp k) p f fun i => 1 / 2 ^ k i

/-- At `k = 0` the mixed modulus is the norm. -/
theorem lpMixedModulus_zero (L : ℕ) (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    lpMixedModulus p L f 0 = ‖f‖ₑ := by
  rw [lpMixedModulus, mixedSupp_zero, mixedModulus_empty, Lp.eNorm_def]

/-- The mixed modulus on `L_p` is subadditive. -/
theorem lpMixedModulus_add_le (L : ℕ) (f g : Lp ℂ p (volume : Measure (Fin d → ℝ)))
    (k : Fin d → ℕ) :
    lpMixedModulus p L (f + g) k ≤ lpMixedModulus p L f k + lpMixedModulus p L g k := by
  rw [lpMixedModulus, mixedModulus_congr_ae (Lp.coeFn_add f g)]
  exact mixedModulus_add_le Fact.out L _ _ _ _

/-- `Ω^{e(k)}_L(f, 2^(-k))_p ≤ 2^(Ld) ‖f‖_p`. -/
theorem lpMixedModulus_le (L : ℕ) (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) (k : Fin d → ℕ) :
    lpMixedModulus p L f k ≤ 2 ^ (L * d) * ‖f‖ₑ := by
  rw [Lp.eNorm_def]
  refine (mixedModulus_le (Lp.aestronglyMeasurable f) Fact.out L _ _).trans
    (mul_le_mul' (pow_le_pow_right₀ one_le_two (Nat.mul_le_mul_left L ?_)) le_rfl)
  exact (Finset.card_le_univ _).trans (Fintype.card_fin d).le

/-- The mixed modulus of `0` vanishes. -/
theorem lpMixedModulus_zero_left (L : ℕ) (k : Fin d → ℕ) :
    lpMixedModulus p L (0 : Lp ℂ p (volume : Measure (Fin d → ℝ))) k = 0 :=
  le_antisymm ((lpMixedModulus_le L 0 k).trans (by simp)) bot_le

variable (p) in
/-- The **Besov quasi-norm of dominating mixed smoothness by differences**,
`‖(2^(s|k|_1) Ω^{e(k)}_L(f, 2^(-k))_p)_{k ∈ ℕ^d}‖_{ℓ_q(ℕ^d)}`. -/
noncomputable def mixedModNorm (L : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) : ℝ≥0∞ :=
  lqNorm q fun k => mixedWeight s k * lpMixedModulus p L f k

/-- The norm of `f` is bounded by the mixed quasi-norm (the term `k = 0`). -/
theorem enorm_le_mixedModNorm (L : ℕ) (s : ℝ) {q : ℝ≥0∞} (hq : q ≠ 0)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) : ‖f‖ₑ ≤ mixedModNorm p L s q f := by
  have h := ENNReal.le_lqNorm hq (fun k => mixedWeight s k * lpMixedModulus p L f k) 0
  simp only [mixedWeight, Pi.zero_apply, ENNReal.dyadicWeight_zero_right, Finset.prod_const_one,
    one_mul, lpMixedModulus_zero] at h
  exact h

end Rd
