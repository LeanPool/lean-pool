/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Payoff

/-!
# Excluding an improvement after completion

This is the scalar contradiction at the end of the proof of the main theorem.
The inequality in `hb` is precisely the conclusion of the collision-deletion
lemma compared to the reward of the chosen terminal decomposition.
-/

@[expose] public section

namespace Egyptian.Payoff

/-- `t` is the reciprocal of the reference error and `h` the competitor's error.
With repeated denominators no deletions and no asymptotic cutoff are needed. -/
theorem no_better_weak {t h : ℝ} (ht : 1 ≤ t) (hh : 0 < h)
    (hB : value (1 / h) ≤ value t) : 1 / t ≤ h := by
  by_contra! he
  have ht' : 0 < t := by linarith
  have hl : t < 1/h := (lt_div_iff₀ hh).2 (by
    have := (lt_div_iff₀ ht').1 he
    linarith)
  exact (not_lt_of_ge hB) (value_strictMonoOn ht (ht.trans hl.le) hl)

/-- For distinct denominators, deletions can double the error at each restart.
The paper's cutoff still excludes a better competitor even at maximal loss. -/
theorem no_better_strict {t h h' : ℝ} {r n : ℕ} (ht : 8 < t)
    (hg : 2 * (n : ℝ) * Real.log 2 < Real.log t) (hr : r ≤ n)
    (hp : 0 < h') (hdel : h' ≤ 2 ^ r * h)
    (hb : (2 : ℝ) ^ r * value (1 / h') ≤ value t) : 1 / t ≤ h := by
  by_contra! he
  have ht' : 0 < t := by linarith
  have hd : 0 < (2:ℝ)^r := by positivity
  have hlt : h' < 2^r / t := by
    simpa [div_eq_mul_inv] using hdel.trans_lt (mul_lt_mul_of_pos_left he hd)
  have hrec : t / 2^r < 1/h' := by
    rw [div_lt_div_iff₀ hd hp]
    have := (lt_div_iff₀ ht').1 hlt
    linarith
  obtain ⟨h1, hs⟩ := deletion_scaling ht hr hg
  have hH := value_strictMonoOn h1 (h1.trans hrec.le) hrec
  exact (not_lt_of_ge hb) (hs.trans_lt (mul_lt_mul_of_pos_left hH hd))

end Egyptian.Payoff

namespace Egyptian

/-- Deleting a collision is an operation on a specific occurrence, even if the
input contains repeated denominators. Its contribution is added to the error. -/
theorem error_erase {q : ℚ} {ds : List ℕ} {d : ℕ} (hd : d ∈ ds) :
    q - recipSum (ds.erase d) = q - recipSum ds + unit d := by
  have hs := ((List.perm_cons_erase hd).map unit).sum_eq
  change recipSum ds = unit d + recipSum (ds.erase d) at hs
  linarith

/-- Collision-restart part of the completion lemma. At each restart a successful
completion ends the process. A collision supplies an original denominator whose
contribution is strictly smaller than the current error. The available factor
of two per denominator keeps every intermediate error at most one. -/
theorem collision_restarts {q : ℚ} (good : List ℕ → Prop) (ds : List ℕ)
    (hpos : 0 < q - recipSum ds)
    (hbudget : (2 : ℚ) ^ ds.length * (q - recipSum ds) ≤ 1)
    (step : ∀ bs, bs.Sublist ds → 0 < q - recipSum bs → q - recipSum bs ≤ 1 →
      good bs ∨ ∃ d ∈ bs, unit d < q - recipSum bs) :
    ∃ bs, bs.Sublist ds ∧ good bs ∧
      q - recipSum bs ≤ 2^(ds.length-bs.length) * (q-recipSum ds) := by
  have hsmall : q - recipSum ds ≤ 1 := by
    have hpow : 1 ≤ (2:ℚ)^ds.length := one_le_pow₀ (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right hpow hpos.le]
  rcases step ds (List.Sublist.refl _) hpos hsmall with done | ⟨d, hd, hcoll⟩
  · exact ⟨ds, List.Sublist.refl _, done, by simp⟩
  · let cs := ds.erase d
    have hcs : cs.Sublist ds := List.erase_sublist
    have hn : cs.length + 1 = ds.length := by
      dsimp [cs]; rw [List.length_erase_of_mem hd]
      have := List.length_pos_of_mem hd
      omega
    have he : q-recipSum cs = q-recipSum ds + unit d := error_erase hd
    have hu : 0 ≤ unit d := by unfold unit; positivity
    have hpos' : 0 < q-recipSum cs := by linarith
    have hdouble : q-recipSum cs ≤ 2*(q-recipSum ds) := by linarith
    have hb : (2:ℚ)^cs.length * (q-recipSum cs) ≤ 1 := by
      rw [← hn, pow_succ] at hbudget
      nlinarith [mul_le_mul_of_nonneg_left hdouble
        (show 0 ≤ (2:ℚ)^cs.length by positivity)]
    obtain ⟨bs, hbcs, hgood, hbound⟩ := collision_restarts good cs hpos' hb
      (fun bs hs => step bs (hs.trans hcs))
    refine ⟨bs, hbcs.trans hcs, hgood, ?_⟩
    have hlen := hbcs.length_le
    have hexp : ds.length - bs.length = cs.length - bs.length + 1 := by omega
    rw [hexp, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hdouble
      (show 0 ≤ (2:ℚ)^(cs.length-bs.length) by positivity)]
termination_by ds.length
decreasing_by change cs.length < ds.length; omega

end Egyptian
