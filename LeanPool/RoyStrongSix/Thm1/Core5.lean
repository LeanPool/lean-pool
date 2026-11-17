/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.Thm1.Core4
public import LeanPool.RoyStrongSix.Thm1.InterpDet

/-!
# The core of Theorem 1, part 5: the analytic side of the independent branch

* `ιV`: a linear isomorphism `ℂⁿ ≅ V`, viewed as a map into `E` (`n = dim V`).
* `fC m = evalExp(X^m) ∘ ιV`: the auxiliary functions on `ℂⁿ`.
* `jetOf r`: the jet of a row. Its directions are `ιV⁻¹(wb_j)` in *reversed* word order, its point
  is `ιV⁻¹(Σ sᵢηᵢ)`.
* `entry_one`: `entry (fC m) (jetOf r) 1 = (interpMatrix r m : ℂ)`.
* `entry_bound`: on `|z| = 2`,
  `‖entry‖ ≤ (Hd (L₀+L₁))^{T_J} (1 + 2ℓS H₀)^{L₀} exp(2ℓS H₁)^{L₁}`.
-/

@[expose] public section

namespace LeanPool

open Module Submodule _root_.MvPolynomial NumberField
open StrongSix.Roy
open scoped ContDiff

namespace StrongSix.Thm1

theorem ofFn_rev_reverse {α : Type*} {k : ℕ} (f : Fin k → α) :
    (List.ofFn fun a => f (Fin.rev a)).reverse = List.ofFn f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
  congr 1
  ext
  simp only [Fin.val_rev]
  simp at h2
  omega

variable {d0 d1 : ℕ} (V : Submodule ℂ (E d0 d1))

/-- `ℂⁿ ≅ V ⊂ E`. -/
noncomputable def ιV : (Fin (finrank ℂ V) → ℂ) →L[ℂ] E d0 d1 :=
  LinearMap.toContinuousLinearMap (V.subtype ∘ₗ (Module.finBasis ℂ V).equivFun.symm.toLinearMap)

/-- Coordinates of a point of `V`. -/
noncomputable def preV (v : E d0 d1) (hv : v ∈ V) : Fin (finrank ℂ V) → ℂ :=
  (Module.finBasis ℂ V).equivFun ⟨v, hv⟩

theorem ιV_preV (v : E d0 d1) (hv : v ∈ V) : ιV V (preV V v hv) = v := by
  simp [ιV, preV]

variable {ℓ t : ℕ} {η : Fin ℓ → E d0 d1} (D : ∀ i, PtData d0 d1 (η i))
  (wb : Fin t → LieG Qb d0 d1)

/-- The auxiliary function `X^m` on `ℂⁿ`. -/
noncomputable def fC {L0 L1 : ℕ} (m : Mono d0 d1 L0 L1) : (Fin (finrank ℂ V) → ℂ) → ℂ :=
  evalExp (monomial m.exps (1 : ℂ)) ∘ ιV V

theorem contDiff_fC {L0 L1 : ℕ} (m : Mono d0 d1 L0 L1) : ContDiff ℂ ω (fC V m) :=
  contDiff_evalExp_comp _ _

theorem γpt_mem (hηV : ∀ i, η i ∈ V) (s : Fin ℓ → ℕ) : γpt η s ∈ V :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hηV i)

/-- The jet of a row. -/
noncomputable def jetOf (hηV : ∀ i, η i ∈ V) (hwV : ∀ j, inclL d0 d1 (wb j) ∈ V) {TJ S : ℕ}
    (r : Row t ℓ TJ S) : Jet (finrank ℂ V) where
  t := r.1.1
  w := fun a => preV V _ (hwV (r.1.2 (Fin.rev a)))
  ζ := preV V _ (γpt_mem V hηV r.pt)

/-- The analytic entry is `evalExp` of the derivation word at `z · γ`. -/
theorem entry_jetOf (hηV : ∀ i, η i ∈ V) (hwV : ∀ j, inclL d0 d1 (wb j) ∈ V) {TJ S L0 L1 : ℕ}
    (r : Row t ℓ TJ S) (m : Mono d0 d1 L0 L1) (z : ℂ) :
    entry (fC V m) (jetOf V wb hηV hwV r) z =
      evalExp (invDers (r.word.map fun j => inclL d0 d1 (wb j)) (monomial m.exps 1))
        (z • γpt η r.pt) := by
  unfold entry fC jetOf
  rw [iteratedFDeriv_evalExp_comp, map_smul, ιV_preV]
  congr 2
  have : (List.ofFn fun a => ιV V (preV V _ (hwV (r.1.2 (Fin.rev a))))) =
      List.ofFn fun a => inclL d0 d1 (wb (r.1.2 (Fin.rev a))) := by
    congr 1; funext a; rw [ιV_preV]
  rw [this, ofFn_rev_reverse (fun a => inclL d0 d1 (wb (r.1.2 a))), Row.word, List.map_ofFn]
  rfl

/-- `algebraMap Qbar ℂ` of a `Qbar`-evaluation is the complex evaluation at `exp_G γ`. -/
theorem algebraMap_interpMatrix {TJ S L0 L1 : ℕ} (r : Row t ℓ TJ S) (m : Mono d0 d1 L0 L1) :
    algebraMap Qb ℂ (interpMatrix D wb TJ S L0 L1 r m) =
      evalExp (invDers (r.word.map fun j => inclL d0 d1 (wb j)) (monomial m.exps 1))
        (γpt η r.pt) := by
  unfold interpMatrix evalExp
  rw [map_eval_hom, map_invDers, map_monomial, map_one]
  have hw : (r.word.map wb).map (fun w => ((fun i => algebraMap Qb ℂ (w.1 i),
      fun j => algebraMap Qb ℂ (w.2 j)) : LieG ℂ d0 d1)) = r.word.map fun j => inclL d0 d1 (wb
        j) := by
    rw [List.map_map]; rfl
  have hg : (fun v => algebraMap Qb ℂ ((gpt D r.pt).coords v)) = expCoords (γpt η r.pt) := by
    funext v
    cases v with
    | inl k => exact gpt_rel1 D r.pt k
    | inr j => exact gpt_rel2 D r.pt j
  rw [hw, hg]

/-- **The value at `z = 1`.** -/
theorem entry_one (hηV : ∀ i, η i ∈ V) (hwV : ∀ j, inclL d0 d1 (wb j) ∈ V) {TJ S L0 L1 : ℕ}
    (r : Row t ℓ TJ S) (m : Mono d0 d1 L0 L1) :
    entry (fC V m) (jetOf V wb hηV hwV r) 1 = algebraMap Qb ℂ (interpMatrix D wb TJ S L0 L1 r m)
      := by
  rw [entry_jetOf, one_smul, algebraMap_interpMatrix]

/-! ### The bound on the circle -/

theorem norm_γpt_fst_le {H0 : ℝ} (hH0 : ∀ i k, ‖(η i).1 k‖ ≤ H0) {S : ℕ}
    {s : Fin ℓ → ℕ} (hs : ∀ i, s i ≤ S) (k : Fin d0) : ‖(γpt η s).1 k‖ ≤ ℓ * S * H0 := by
  simp only [γpt, Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc ‖∑ i, (s i : ℂ) * (η i).1 k‖ ≤ ∑ i, ‖(s i : ℂ) * (η i).1 k‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin ℓ, (S : ℝ) * H0 := Finset.sum_le_sum fun i _ => by
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul (by exact_mod_cast hs i) (hH0 i k) (norm_nonneg _) (by positivity)
    _ = ℓ * S * H0 := by simp; ring

theorem norm_γpt_snd_le {H1 : ℝ} (hH1 : ∀ i j, ‖(η i).2 j‖ ≤ H1) {S : ℕ}
    {s : Fin ℓ → ℕ} (hs : ∀ i, s i ≤ S) (j : Fin d1) : ‖(γpt η s).2 j‖ ≤ ℓ * S * H1 := by
  simp only [γpt, Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc ‖∑ i, (s i : ℂ) * (η i).2 j‖ ≤ ∑ i, ‖(s i : ℂ) * (η i).2 j‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin ℓ, (S : ℝ) * H1 := Finset.sum_le_sum fun i _ => by
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul (by exact_mod_cast hs i) (hH1 i j) (norm_nonneg _) (by positivity)
    _ = ℓ * S * H1 := by simp; ring

section Circle

variable (K : IntermediateField ℚ ℂ) (hmem : ∀ x, ((dataFam D wb x : Qb) : ℂ) ∈ K)

/-- **The entries on the circle `|z| = 2`.** -/
theorem entry_bound [NumberField K] (hηV : ∀ i, η i ∈ V) (hwV : ∀ j, inclL d0 d1 (wb j) ∈ V)
    (δ : ℕ) {Hd : ℝ} (hHd : 1 ≤ Hd)
    (hδw1 : ∀ j k, IsIntegral ℤ ((δ : K) * (wK D wb K hmem j).1 k))
    (hδw2 : ∀ j k, IsIntegral ℤ ((δ : K) * (wK D wb K hmem j).2 k))
    (hHw1 : ∀ j k, house ((wK D wb K hmem j).1 k) ≤ Hd)
    (hHw2 : ∀ j k, house ((wK D wb K hmem j).2 k) ≤ Hd)
    {H0 H1 : ℝ} (hH0' : 0 ≤ H0) (hH1' : 0 ≤ H1) (hH0 : ∀ i k, ‖(η i).1 k‖ ≤ H0)
    (hH1 : ∀ i j, ‖(η i).2 j‖ ≤ H1)
    {TJ S L0 L1 : ℕ} (hL0 : 1 ≤ L0) (r : Row t ℓ TJ S) (m : Mono d0 d1 L0 L1) (z : ℂ)
    (hz : ‖z‖ = 2) :
    ‖entry (fC V m) (jetOf V wb hηV hwV r) z‖ ≤
      (Hd * (L0 + L1)) ^ TJ * (1 + 2 * (ℓ * S * H0)) ^ L0 *
        (Real.exp (2 * (ℓ * S * H1))) ^ L1 := by
  set l := r.word.map (wK D wb K hmem) with hl
  have hlen : l.length < TJ := by rw [hl, List.length_map]; exact r.word_length
  have hA : (0 : ℝ) ≤ Hd := by linarith
  have hgood := good_invDers (good_monomial (K := K) m.exps (D0 := L0) (D1 := L1)
      (by simpa [Mono.exps_inl] using m.2.1) (by simpa [Mono.exps_inr] using m.2.2) δ) l hA
    (fun w hw i => by obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw; exact hδw1 j i)
    (fun w hw i => by obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw; exact hδw2 j i)
    (fun w hw i => by obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw; exact hHw1 j i)
    (fun w hw i => by obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw; exact hHw2 j i)
  rw [zero_add, mul_one] at hgood
  have hmap : invDers (r.word.map fun j => inclL d0 d1 (wb j)) (monomial m.exps (1 : ℂ)) =
      map (algebraMap K ℂ) (invDers l (monomial m.exps 1)) := by
    rw [map_invDers, map_monomial, (algebraMap K ℂ).map_one, hl, List.map_map]
    rfl
  rw [entry_jetOf, evalExp, hmap]
  have hS0 : (0 : ℝ) ≤ ℓ * S * H0 := by positivity
  have hS1 : (0 : ℝ) ≤ ℓ * S * H1 := by positivity
  have hX1 : (1 : ℝ) ≤ 1 + 2 * (ℓ * S * H0) := by linarith
  have hY1 : (1 : ℝ) ≤ Real.exp (2 * (ℓ * S * H1)) := Real.one_le_exp (by linarith)
  have hx : ∀ k, ‖expCoords (z • γpt η r.pt) (Sum.inl k)‖ ≤ 1 + 2 * (ℓ * S * H0) := by
    intro k
    simp only [expCoords, Sum.elim_inl, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, norm_mul, hz]
    have := norm_γpt_fst_le hH0 (fun i => r.pt_le i) k
    linarith
  have hy : ∀ j, ‖expCoords (z • γpt η r.pt) (Sum.inr j)‖ ≤ Real.exp (2 * (ℓ * S * H1)) := by
    intro j
    simp only [expCoords, Sum.elim_inr, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul, hz]
    have := norm_γpt_snd_le hH1 (fun i => r.pt_le i) j
    linarith
  have h := norm_eval_map_le hgood (algebraMap K ℂ) (expCoords (z • γpt η r.pt)) hX1 hY1 hx hy
  have hAL : (1 : ℝ) ≤ Hd * (L0 + L1) := by
    have : (1 : ℝ) ≤ L0 := by exact_mod_cast hL0
    nlinarith [Nat.cast_nonneg (α := ℝ) L1]
  refine h.trans ?_
  gcongr

end Circle

end StrongSix.Thm1

end LeanPool
