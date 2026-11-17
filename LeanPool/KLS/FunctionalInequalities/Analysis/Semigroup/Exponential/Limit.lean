/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Exponential.Contraction
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Strong limits of commuting nonnegative operator exponentials

Commuting bounded nonnegative operators on a complete real Hilbert space satisfy
`‖exp (-t • A) f - exp (-t • B) f‖ ≤ t * ‖A f - B f‖` for `t ≥ 0`.
For a pairwise commuting family, a Cauchy condition on a dense set yields a strong
positive-parameter limit of the exponentials. The dense-set argument uses contraction.
The auxiliary Cauchy-limit construction needs only a complete normed group.
-/

@[expose] public section

noncomputable section

open InnerProductSpace

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup

section Contraction

variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]

/--
Restatement of resolvent contraction (`norm_exp_neg_smul_apply_le`) for a **nonpositive** scalar: if
`L` is
bounded and nonnegative and `c ≤ 0`, then `exp (c • L)` is a pointwise contraction. -/
theorem norm_exp_smul_apply_le_of_nonpos (L : H₀ →L[ℝ] H₀) (hL : ∀ f, 0 ≤ ⟪L f, f⟫) {c : ℝ}
    (hc : c ≤ 0) (f : H₀) : ‖NormedSpace.exp (c • L) f‖ ≤ ‖f‖ := by
  have h := norm_exp_neg_smul_apply_le L hL (neg_nonneg.mpr hc) f
  rwa [neg_neg] at h

/--
Restatement of resolvent contraction (`norm_exp_neg_smul_apply_le`) with the sign on the
**operator**: if `L`
is bounded and nonnegative and `0 ≤ c`, then `exp (c • (-L))` is a pointwise contraction. This is
the normal form produced by `hasDerivAt_exp_smul_const` along the orbit of `-L`. -/
theorem norm_exp_smul_neg_apply_le (L : H₀ →L[ℝ] H₀) (hL : ∀ f, 0 ≤ ⟪L f, f⟫) {c : ℝ}
    (hc : 0 ≤ c) (f : H₀) : ‖NormedSpace.exp (c • (-L)) f‖ ≤ ‖f‖ := by
  have h := norm_exp_neg_smul_apply_le L hL hc f
  rwa [neg_smul, ← smul_neg] at h

/-- **Exponential difference bound.** Two commuting bounded nonnegative operators have
exponentials that differ, pointwise at `f` and for `t ≥ 0`, by at most `t ‖A f - B f‖`:
`‖exp (-t • A) f - exp (-t • B) f‖ ≤ t * ‖A f - B f‖`.

The proof differentiates the interpolation path `τ ↦ exp (τ • (-A)) (exp ((τ - t) • B) f)` on
`[0, t]` and applies the mean value inequality; see the module docstring. Every hypothesis is
used. -/
theorem norm_exp_neg_smul_sub_le (A B : H₀ →L[ℝ] H₀) (hA : ∀ f, 0 ≤ ⟪A f, f⟫)
    (hB : ∀ f, 0 ≤ ⟪B f, f⟫) (hAB : A.comp B = B.comp A) {t : ℝ} (ht : 0 ≤ t) (f : H₀) :
    ‖NormedSpace.exp (-t • A) f - NormedSpace.exp (-t • B) f‖ ≤ t * ‖A f - B f‖ := by
  have hcomm : Commute A B := hAB
  have hmove : ∀ (c : ℝ) (v : H₀),
      A (NormedSpace.exp (c • B) v) = NormedSpace.exp (c • B) (A v) := by
    intro c v
    have h : Commute A (NormedSpace.exp (c • B)) := (hcomm.smul_right c).exp_right
    exact congrArg (fun M : H₀ →L[ℝ] H₀ => M v) h
  have hderiv : ∀ τ : ℝ, HasDerivAt
      (fun σ : ℝ => NormedSpace.exp (σ • (-A)) (NormedSpace.exp ((σ - t) • B) f))
      (NormedSpace.exp (τ • (-A)) (NormedSpace.exp ((τ - t) • B) (B f - A f))) τ := by
    intro τ
    have hc : HasDerivAt (fun σ : ℝ => NormedSpace.exp (σ • (-A)))
        (NormedSpace.exp (τ • (-A)) * (-A)) τ := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) τ
    have hE : HasDerivAt (fun σ : ℝ => NormedSpace.exp ((σ - t) • B))
        (NormedSpace.exp ((τ - t) • B) * B) τ := by
      have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) B (τ - t)).scomp τ
        ((hasDerivAt_id τ).sub_const t)
      simpa [Function.comp_def] using h
    have hu : HasDerivAt (fun σ : ℝ => NormedSpace.exp ((σ - t) • B) f)
        (NormedSpace.exp ((τ - t) • B) (B f)) τ := by
      have h := hE.clm_apply (hasDerivAt_const τ f)
      simpa using h
    refine (hc.clm_apply hu).congr_deriv ?_
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, neg_apply, hmove]
    simp only [map_sub, map_neg]
    abel
  have hbd : ∀ τ ∈ Set.Ico (0 : ℝ) t,
      ‖NormedSpace.exp (τ • (-A)) (NormedSpace.exp ((τ - t) • B) (B f - A f))‖ ≤
        ‖A f - B f‖ := by
    intro τ hτ
    calc ‖NormedSpace.exp (τ • (-A)) (NormedSpace.exp ((τ - t) • B) (B f - A f))‖
        ≤ ‖NormedSpace.exp ((τ - t) • B) (B f - A f)‖ :=
          norm_exp_smul_neg_apply_le A hA hτ.1 _
      _ ≤ ‖B f - A f‖ :=
          norm_exp_smul_apply_le_of_nonpos B hB (sub_nonpos.mpr hτ.2.le) _
      _ = ‖A f - B f‖ := norm_sub_rev _ _
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun σ : ℝ => NormedSpace.exp (σ • (-A)) (NormedSpace.exp ((σ - t) • B) f))
    (f' := fun τ : ℝ => NormedSpace.exp (τ • (-A)) (NormedSpace.exp ((τ - t) • B) (B f - A f)))
    (C := ‖A f - B f‖) (fun x _ => (hderiv x).hasDerivWithinAt) hbd t
    (Set.right_mem_Icc.mpr ht)
  simp only [sub_self, zero_smul, NormedSpace.exp_zero, one_apply_eq_self, zero_sub,
    sub_zero] at hmvt
  rw [neg_smul, ← smul_neg, mul_comm]
  exact hmvt

end Contraction

section Completeness

variable {H₀ : Type*} [NormedAddCommGroup H₀] [CompleteSpace H₀]

/-- A family `u s hs` indexed by the positive reals that is Cauchy as `s ↓ 0`, in the `ε`–`δ`
form, converges as `s ↓ 0`, again in the `ε`–`δ` form.

Only completeness of the normed group is used; no inner product, no operators. This is the
completeness step of `exists_limit_exp_neg_smul`. -/
theorem exists_limit_of_cauchy_along_pos (u : ∀ s : ℝ, 0 < s → H₀)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (s r : ℝ) (hs : 0 < s) (hr : 0 < r), s < δ → r < δ → ‖u s hs - u r hr‖ < ε) :
    ∃ g : H₀, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (s : ℝ) (hs : 0 < s), s < δ → ‖u s hs - g‖ < ε := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hsmall : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 / ((n : ℝ) + 1) < δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hcs : CauchySeq fun n : ℕ => u (1 / ((n : ℝ) + 1)) (hpos n) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hu ε hε
    obtain ⟨N, hN⟩ := hsmall δ hδ
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    exact hδ' _ _ _ _ (hN m hm) (hN n hn)
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨g, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hδ'⟩ := hu (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := hsmall δ hδ
  rw [Metric.tendsto_atTop] at hg
  obtain ⟨N', hN'⟩ := hg (ε / 2) (by linarith)
  refine ⟨δ, hδ, fun s hs hsδ => ?_⟩
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, N ≤ n ∧ N' ≤ n :=
    ⟨max N N', le_max_left _ _, le_max_right _ _⟩
  have h1 : ‖u s hs - u (1 / ((n : ℝ) + 1)) (hpos n)‖ < ε / 2 :=
    hδ' _ _ _ _ hsδ (hN n hn1)
  have h2 : ‖u (1 / ((n : ℝ) + 1)) (hpos n) - g‖ < ε / 2 := by
    have h := hN' n hn2
    rwa [dist_eq_norm] at h
  have h3 := norm_add_le (u s hs - u (1 / ((n : ℝ) + 1)) (hpos n))
    (u (1 / ((n : ℝ) + 1)) (hpos n) - g)
  rw [sub_add_sub_cancel] at h3
  linarith

end Completeness

section Limit

variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]

/-- **The corrected abstract adjoint-product identification.** Let `L s hs` be bounded,
nonnegative and pairwise commuting for `s > 0`, and suppose the values `L s hs v` are Cauchy as `s ↓
0` for every `v` in a
dense set `D`. Then for every `f : H₀` and every `t ≥ 0` the family `exp (-t • L s hs) f`
converges as `s ↓ 0`.

`norm_exp_neg_smul_sub_le` gives the Cauchy property of `exp (-t • L s hs) v` for `v ∈ D`, the
contraction bound `norm_exp_neg_smul_apply_le` transports it to every `f` by an `ε/3` argument, and
`exists_limit_of_cauchy_along_pos` produces the limit. -/
theorem exists_limit_exp_neg_smul (L : ∀ s : ℝ, 0 < s → H₀ →L[ℝ] H₀)
    (hL : ∀ (s : ℝ) (hs : 0 < s) (f : H₀), 0 ≤ ⟪L s hs f, f⟫)
    (hcomm :
      ∀ (s r : ℝ) (hs : 0 < s) (hr : 0 < r), (L s hs).comp (L r hr) = (L r hr).comp (L s hs))
    (D : Set H₀) (hD : Dense D)
    (hC :
      ∀ v ∈ D,
        ∀ ε : ℝ,
          0 < ε →
            ∃ δ : ℝ,
              0 < δ ∧
                ∀ (s r : ℝ) (hs : 0 < s) (hr : 0 < r),
                  s < δ → r < δ → ‖L s hs v - L r hr v‖ < ε)
    (f : H₀) {t : ℝ} (ht : 0 ≤ t) :
    ∃ g : H₀,
      ∀ ε : ℝ,
        0 < ε →
          ∃ δ : ℝ,
            0 < δ ∧ ∀ (s : ℝ) (hs : 0 < s), s < δ → ‖NormedSpace.exp (-t • L s hs) f - g‖ < ε := by
  -- Step 1: the Cauchy property on the dense set, from `norm_exp_neg_smul_sub_le`.
  have key :
    ∀ v ∈ D,
      ∀ ε : ℝ,
        0 < ε →
          ∃ δ : ℝ,
            0 < δ ∧
              ∀ (s r : ℝ) (hs : 0 < s) (hr : 0 < r),
                s < δ →
                  r < δ →
                    ‖NormedSpace.exp (-t • L s hs) v - NormedSpace.exp (-t • L r hr) v‖ < ε := by
    intro v hv ε hε
    have ht1 : (0 : ℝ) < t + 1 := by linarith
    have hε' : 0 < ε / (t + 1) := by positivity
    obtain ⟨δ, hδ, hδ'⟩ := hC v hv (ε / (t + 1)) hε'
    refine ⟨δ, hδ, fun s r hs hr hsδ hrδ => ?_⟩
    have h6 :=
      norm_exp_neg_smul_sub_le (L s hs) (L r hr) (hL s hs) (hL r hr) (hcomm s r hs hr) ht v
    have h2 : t * ‖L s hs v - L r hr v‖ ≤ t * (ε / (t + 1)) :=
      mul_le_mul_of_nonneg_left (hδ' s r hs hr hsδ hrδ).le ht
    have h3 : t * (ε / (t + 1)) < ε := by
      calc
        t * (ε / (t + 1)) < (t + 1) * (ε / (t + 1)) := mul_lt_mul_of_pos_right (by linarith) hε'
        _ = ε := by field_simp
    linarith
  -- Step 2: the Cauchy property for an arbitrary vector, by an `ε/3` argument.
  have general :
    ∀ ε : ℝ,
      0 < ε →
        ∃ δ : ℝ,
          0 < δ ∧
            ∀ (s r : ℝ) (hs : 0 < s) (hr : 0 < r),
              s < δ →
                r < δ →
                  ‖NormedSpace.exp (-t • L s hs) f - NormedSpace.exp (-t • L r hr) f‖ < ε := by
    intro ε hε
    obtain ⟨v, hvD, hvf⟩ := Metric.mem_closure_iff.mp (hD f) (ε / 3) (by linarith)
    obtain ⟨δ, hδ, hδ'⟩ := key v hvD (ε / 3) (by linarith)
    refine ⟨δ, hδ, fun s r hs hr hsδ hrδ => ?_⟩
    have hfv : ‖f - v‖ < ε / 3 := by rwa [← dist_eq_norm]
    have c1 : ‖NormedSpace.exp (-t • L s hs) f - NormedSpace.exp (-t • L s hs) v‖ < ε / 3 := by
      rw [← map_sub]
      exact lt_of_le_of_lt (norm_exp_neg_smul_apply_le (L s hs) (hL s hs) ht _) hfv
    have c2 : ‖NormedSpace.exp (-t • L r hr) v - NormedSpace.exp (-t • L r hr) f‖ < ε / 3 := by
      rw [← map_sub]
      refine lt_of_le_of_lt (norm_exp_neg_smul_apply_le (L r hr) (hL r hr) ht _) ?_
      rwa [norm_sub_rev]
    have c3 := hδ' s r hs hr hsδ hrδ
    have h4 :=
      dist_triangle4 (NormedSpace.exp (-t • L s hs) f) (NormedSpace.exp (-t • L s hs) v)
        (NormedSpace.exp (-t • L r hr) v) (NormedSpace.exp (-t • L r hr) f)
    simp only [dist_eq_norm] at h4
    linarith
  exact exists_limit_of_cauchy_along_pos (fun s hs => NormedSpace.exp (-t • L s hs) f) general

end Limit

end FunctionalInequalities.Analysis.Semigroup
