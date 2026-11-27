/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolWeakLimit
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite selection from common weak limits

For every requested finite size, weak convergence permits a set of samples
with arbitrarily small pairwise centered inner products. Finitely many
eventual side conditions may be imposed at the same time, and the selected
positions can be made distinct. The squared norm of their average is bounded
by `4 / M + ε` when the samples and their limits lie in the unit ball.

This is the finite selection used to prove termination of the pool search.
It does not require an effective modulus of weak convergence.
-/

@[expose] public section

namespace Klr.Pool

open Filter
open scoped Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Weak convergence supplies arbitrarily large finite sets of nearly
orthogonal centered vectors, with all eventual side conditions retained. -/
theorem exists_finite_weak_samples (u : ℕ → ℕ → E) (g : ℕ → E)
    (hu : ∀ i, WeaklyConverges (u i) (g i))
    (a : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (P : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (ℓ : ℕ)
    {ε : ℝ} (hε : 0 < ε) (M : ℕ) :
    ∃ F : Finset ℕ, F.card = M ∧
      (∀ n ∈ F, P n) ∧ Set.InjOn a F ∧
      ∀ i < ℓ, ∀ n ∈ F, ∀ m ∈ F, n ≠ m →
        inner ℝ (u i n - g i) (u i m - g i) < ε := by
  classical
  induction M with
  | zero => exact ⟨∅, by simp, by simp, by simp, by simp⟩
  | succ M ih =>
    obtain ⟨F, hcard, hPF, hAF, hcrossF⟩ := ih
    have hcross : ∀ᶠ k : ℕ in atTop,
        ∀ i : Fin ℓ, ∀ m ∈ F,
          inner ℝ (u i k - g i) (u i m - g i) < ε := by
      apply Filter.eventually_all.mpr
      intro i
      apply (Filter.eventually_all_finset F).mpr
      intro m hm
      have ht : Tendsto (fun k => inner ℝ (u i k - g i) (u i m - g i))
          atTop (𝓝 0) := by
        simpa only [inner_sub_left, sub_self] using
          (hu i (u i m - g i)).sub
            (tendsto_const_nhds (x := inner ℝ (g i) (u i m - g i)))
      exact ht.eventually (gt_mem_nhds hε)
    have hlarge : ∀ᶠ k : ℕ in atTop, F.sup a < a k :=
      ha.eventually (eventually_gt_atTop (F.sup a))
    obtain ⟨k, hPk, hk, hC⟩ := (hP.and (hlarge.and hcross)).exists
    have hbig : ∀ n ∈ F, a n < a k := fun n hn =>
      lt_of_le_of_lt (Finset.le_sup (f := a) hn) hk
    have hkF : k ∉ F := fun hkF => (lt_irrefl (a k)) (hbig k hkF)
    refine ⟨insert k F, by simp [hkF, hcard], ?_, ?_, ?_⟩
    · intro n hn
      rcases Finset.mem_insert.mp hn with rfl | hn
      · exact hPk
      · exact hPF n hn
    · intro n hn m hm he
      by_cases hnk : n = k
      · subst n
        by_cases hmk : m = k
        · exact hmk.symm
        · have hmF := (Finset.mem_insert.mp hm).resolve_left hmk
          exact False.elim ((ne_of_lt (hbig m hmF)) he.symm)
      · have hnF := (Finset.mem_insert.mp hn).resolve_left hnk
        by_cases hmk : m = k
        · subst m
          exact False.elim ((ne_of_lt (hbig n hnF)) he)
        · exact hAF hnF ((Finset.mem_insert.mp hm).resolve_left hmk) he
    · intro i hi n hn m hm hne
      by_cases hnk : n = k
      · subst n
        have hmF := (Finset.mem_insert.mp hm).resolve_left (Ne.symm hne)
        exact hC ⟨i, hi⟩ m hmF
      · have hnF := (Finset.mem_insert.mp hn).resolve_left hnk
        by_cases hmk : m = k
        · subst m
          rw [real_inner_comm]
          exact hC ⟨i, hi⟩ n hnF
        · exact hcrossF i hi n hnF m ((Finset.mem_insert.mp hm).resolve_left hmk) hne

/-- The diagonal contributes at most `4 M`; the off-diagonal terms contribute
at most `ε M²`. The slightly generous constant avoids special indicator algebra. -/
theorem norm_sum_sq_le_of_inner_le (v : ℕ → E) (F : Finset ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) (hv : ∀ n ∈ F, ‖v n‖ ≤ 2)
    (hcross : ∀ n ∈ F, ∀ m ∈ F, n ≠ m → inner ℝ (v n) (v m) ≤ ε) :
    ‖∑ n ∈ F, v n‖ ^ 2 ≤ 4 * (F.card : ℝ) + ε * (F.card : ℝ) ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum]
  calc
    _ ≤ ∑ n ∈ F, ∑ m ∈ F, ((if n = m then (4 : ℝ) else 0) + ε) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      by_cases hnm : n = m
      · subst m
        simp only [↓reduceIte, real_inner_self_eq_norm_sq]
        have h := hv n hn
        nlinarith [norm_nonneg (v n)]
      · simpa [hnm] using hcross n hn m hm hnm
    _ = _ := by
      simp [Finset.sum_add_distrib, Finset.sum_ite_eq, pow_two]
      ring

/-- Quantitative average estimate used in the finite pool witness. -/
theorem norm_average_sq_le_of_inner_le (v : ℕ → E) (F : Finset ℕ)
    (hF : F.Nonempty) {ε : ℝ} (hε : 0 ≤ ε) (hv : ∀ n ∈ F, ‖v n‖ ≤ 2)
    (hcross : ∀ n ∈ F, ∀ m ∈ F, n ≠ m → inner ℝ (v n) (v m) ≤ ε) :
    ‖(F.card : ℝ)⁻¹ • ∑ n ∈ F, v n‖ ^ 2 ≤ 4 / (F.card : ℝ) + ε := by
  have hcard : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcard), mul_pow]
  calc
    _ ≤ (F.card : ℝ)⁻¹ ^ 2 * (4 * (F.card : ℝ) + ε * (F.card : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (norm_sum_sq_le_of_inner_le v F hε hv hcross) (sq_nonneg _)
    _ = _ := by field_simp

/-- For all sufficiently large requested sizes, a finite weak sample has a
small centered average and satisfies every eventual side condition. -/
theorem eventually_exists_finite_weak_average (u : ℕ → ℕ → E) (g : ℕ → E)
    (hu : ∀ i, WeaklyConverges (u i) (g i))
    (hu1 : ∀ i n, ‖u i n‖ ≤ 1) (hg1 : ∀ i, ‖g i‖ ≤ 1)
    (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) (ℓ : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ M : ℕ in atTop, ∀ (P : ℕ → Prop), (∀ᶠ n in atTop, P n) →
      ∃ F : Finset ℕ, F.card = M ∧ (∀ n ∈ F, P n) ∧ Set.InjOn a F ∧
        ∀ i < ℓ, ‖(F.card : ℝ)⁻¹ • ∑ n ∈ F, (u i n - g i)‖ < δ := by
  have hsmall : ∀ᶠ M : ℕ in atTop, 4 / (M : ℝ) + δ ^ 2 / 4 < δ ^ 2 := by
    have ht : Tendsto (fun M : ℕ => 4 / (M : ℝ) + δ ^ 2 / 4)
        atTop (𝓝 (δ ^ 2 / 4)) := by
      simpa using ((tendsto_const_nhds (x := (4 : ℝ))).div_atTop
        tendsto_natCast_atTop_atTop).add_const (δ ^ 2 / 4)
    exact ht.eventually (gt_mem_nhds (by nlinarith [sq_pos_of_pos hδ]))
  filter_upwards [eventually_ge_atTop 1, hsmall] with M hM hsmall
  intro P hP
  obtain ⟨F, hcard, hPF, hinj, hcross⟩ := exists_finite_weak_samples u g hu a ha P hP ℓ
    (show 0 < δ ^ 2 / 4 by positivity) M
  refine ⟨F, hcard, hPF, hinj, ?_⟩
  intro i hi
  have hF : F.Nonempty := Finset.card_pos.mp (by omega)
  have hnorm : ∀ n ∈ F, ‖u i n - g i‖ ≤ 2 := by
    intro n _
    exact (norm_sub_le _ _).trans (by linarith [hu1 i n, hg1 i])
  have hbound := norm_average_sq_le_of_inner_le (fun n => u i n - g i) F hF
    (show 0 ≤ δ ^ 2 / 4 by positivity) hnorm
    (fun n hn m hm hne => (hcross i hi n hn m hm hne).le)
  rw [hcard] at hbound
  have hsq : ‖(F.card : ℝ)⁻¹ • ∑ n ∈ F, (u i n - g i)‖ ^ 2 < δ ^ 2 := by
    rw [hcard]
    exact hbound.trans_lt hsmall
  nlinarith [norm_nonneg ((F.card : ℝ)⁻¹ • ∑ n ∈ F, (u i n - g i))]

end Klr.Pool
