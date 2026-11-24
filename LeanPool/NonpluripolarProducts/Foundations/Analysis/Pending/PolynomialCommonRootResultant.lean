/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Common roots of a polynomial and a family, detected by resultants

Let `f ∈ ℂ[X]` be monic of degree `d` and let `ρ₀, …, ρ_{s-1} ∈ ℂ[X]` have degree at most `d`.
For `μ ∈ ℂ` consider the pencil `g_μ = ∑ⱼ μ^j ρⱼ`. We prove that `f` and all `ρⱼ` have a common
root if and only if the resultants `Res_{d,d}(f, g_l)` vanish for all integers `0 ≤ l ≤ d s`.

The resultant is taken with the *fixed formal degrees* `(d, d)`, independent of the actual degree
of `g_l`.

## Proof

For a monic `f` of degree `d` and `deg g ≤ d`, `Res_{d,d}(f, g)` equals the usual resultant, so
over a field it vanishes iff `f` and `g` are not coprime; over `ℂ` this means that they have a
common root.

* If `t` is a common root of `f` and all `ρⱼ`, it is a root of every `g_μ`.
* Conversely, suppose there is no common root. For each of the at most `d` roots `t` of `f`, the
  polynomial `P_t(μ) = ∑ⱼ ρⱼ(t) μ^j` is nonzero of degree `< s`, so it has at most `s` roots.
  Hence at most `d s` values of `μ` are bad, and some `l ∈ {0, …, d s}` makes `g_l(t) = P_t(l)`
  nonzero at every root `t` of `f`. Then `f` and `g_l` are coprime and `Res_{d,d}(f, g_l) ≠ 0`.

No hypotheses on `d` or `s` are needed.
-/

@[expose] public section

open Polynomial

namespace SGPT.Foundations.Analysis.Pending.PolynomialCommonRootResultant

/-- For monic `f` of degree `d` and `g` of degree at most `d` over a field, the resultant with
formal degrees `(d, d)` vanishes iff `f` and `g` are not coprime. -/
theorem resultant_eq_zero_iff_not_isCoprime {K : Type*} [Field K] {f g : K[X]} {d : ℕ}
    (hf : f.Monic) (hfd : f.natDegree = d) (hg : g.natDegree ≤ d) :
    resultant f g d d = 0 ↔ ¬ IsCoprime f g := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hg
  rw [resultant_add_right_deg _ _ _ _ _ le_rfl, ← hfd, hf.coeff_natDegree, one_pow, one_mul,
    resultant_eq_zero_iff]
  simp [hf.ne_zero]

/-- The resultant with formal degrees `(d, d)` of a monic complex polynomial `f` of degree `d`
and a polynomial `g` of degree at most `d` vanishes iff `f` and `g` have a common root. -/
theorem resultant_eq_zero_iff_exists_common_root {f g : ℂ[X]} {d : ℕ}
    (hf : f.Monic) (hfd : f.natDegree = d) (hg : g.natDegree ≤ d) :
    resultant f g d d = 0 ↔ ∃ t : ℂ, f.eval t = 0 ∧ g.eval t = 0 := by
  rw [resultant_eq_zero_iff_not_isCoprime hf hfd hg,
    isCoprime_iff_aeval_ne_zero_of_isAlgClosed (K := ℂ) (p := f) (q := g)]
  simp

/-- **Common roots via resultants of a pencil.** Let `f ∈ ℂ[X]` be monic of degree `d` and
`ρ : Fin s → ℂ[X]` with `deg ρⱼ ≤ d`. Then `f` and all `ρⱼ` have a common root iff for every
natural `l ≤ d * s` the resultant, with fixed formal degrees `(d, d)`, of `f` and
`∑ⱼ l^j ρⱼ` vanishes. -/
theorem exists_common_root_iff_forall_resultant_eq_zero {f : ℂ[X]} {d s : ℕ}
    (hf : f.Monic) (hfd : f.natDegree = d) (ρ : Fin s → ℂ[X]) (hρ : ∀ j, (ρ j).natDegree ≤ d) :
    (∃ t : ℂ, f.eval t = 0 ∧ ∀ j, (ρ j).eval t = 0) ↔
      ∀ l : ℕ, l ≤ d * s → resultant f (∑ j : Fin s, C ((l : ℂ) ^ (j : ℕ)) * ρ j) d d = 0 := by
  have hdeg : ∀ μ : ℂ, (∑ j : Fin s, C (μ ^ (j : ℕ)) * ρ j).natDegree ≤ d := fun μ =>
    natDegree_sum_le_of_forall_le _ _ fun j _ => natDegree_C_mul_le _ _ |>.trans (hρ j)
  simp_rw [resultant_eq_zero_iff_exists_common_root hf hfd (hdeg _)]
  constructor
  · rintro ⟨t, hft, hρt⟩ l -
    exact ⟨t, hft, by simp [eval_finsetSum, hρt]⟩
  · intro H
    by_contra hno
    simp only [not_exists, not_and, not_forall] at hno
    -- For a root `t` of `f`, the polynomial `P t` in `μ` whose value at `μ` is `g_μ(t)`.
    set P : ℂ → ℂ[X] := fun t => ∑ j : Fin s, C ((ρ j).eval t) * X ^ (j : ℕ) with hP
    have hPeval : ∀ t μ : ℂ, (P t).eval μ = (∑ j : Fin s, C (μ ^ (j : ℕ)) * ρ j).eval t := by
      intro t μ
      simp only [hP, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hPne : ∀ t ∈ f.roots.toFinset, P t ≠ 0 := by
      intro t ht hPt
      rw [Multiset.mem_toFinset, mem_roots hf.ne_zero, IsRoot.def] at ht
      obtain ⟨j, hj⟩ := hno t ht
      apply hj
      have := congrArg (fun p : ℂ[X] => p.coeff (j : ℕ)) hPt
      simpa [hP, coeff_X_pow, Fin.val_inj] using this
    have hPcard : ∀ t, (P t).roots.toFinset.card ≤ s := fun t =>
      (Multiset.toFinset_card_le _).trans <| (card_roots' _).trans <|
        natDegree_sum_le_of_forall_le _ _ fun j _ =>
          (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le _).trans j.isLt.le)
    let B : Finset ℂ := f.roots.toFinset.biUnion fun t => (P t).roots.toFinset
    have hB : B.card < ((Finset.range (d * s + 1)).image (Nat.cast : ℕ → ℂ)).card := by
      rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
      calc B.card ≤ ∑ t ∈ f.roots.toFinset, (P t).roots.toFinset.card := Finset.card_biUnion_le
        _ ≤ ∑ _t ∈ f.roots.toFinset, s := Finset.sum_le_sum fun t _ => hPcard t
        _ = f.roots.toFinset.card * s := by simp
        _ ≤ d * s := by
          gcongr
          exact (Multiset.toFinset_card_le _).trans (hfd ▸ card_roots' f)
        _ < d * s + 1 := Nat.lt_succ_self _
    obtain ⟨μ, hμ, hμB⟩ := Finset.exists_mem_notMem_of_card_lt_card hB
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hμ
    obtain ⟨t, hft, hgt⟩ := H l (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))
    have ht : t ∈ f.roots.toFinset := by
      rw [Multiset.mem_toFinset, mem_roots hf.ne_zero, IsRoot.def]; exact hft
    apply hμB
    refine Finset.mem_biUnion.mpr ⟨t, ht, ?_⟩
    rw [Multiset.mem_toFinset, mem_roots (hPne t ht), IsRoot.def, hPeval]
    exact hgt

end SGPT.Foundations.Analysis.Pending.PolynomialCommonRootResultant
