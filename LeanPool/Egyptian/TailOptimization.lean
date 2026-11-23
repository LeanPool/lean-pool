/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Assembly
public import LeanPool.Egyptian.PayoffCompletion
import Mathlib.Tactic.Positivity.Finset

/-!
# Optimizing all sufficiently long extensions

The two inputs in `compatible_of_terminal_completion` are the maximizing
terminal decomposition and the numerical conclusions of the completion lemma.
The proof constructs a single compatible prefix after the cutoff, comparing
every admissible rival. The real number C is the initial Bellman value, which
equals the discounted payoff of the selected prefix.
-/

@[expose] public section

namespace Egyptian

/-- The consequences of the completion lemma used in the final contradiction.
Here h' is the actual error after the deletions; only its bounds are needed. -/
def CompletionBound (σ : Convention) (q : ℚ) (C : ℝ) : Prop :=
  ∀ (n : ℕ) (ds : List ℕ), Admissible σ q n ds →
    let h : ℝ := (q - recipSum ds : ℚ)
    (match σ with | .weak => h ≤ 1 | .strict => 2^n * h ≤ 1) →
      ∃ r ≤ n, ∃ h' : ℝ, 0 < h' ∧ h' ≤ 2^r * h ∧
        (σ = .weak → r = 0 ∧ h' = h) ∧
        Payoff.value (1/h') / 2^(n-r) ≤ C

private theorem digits_append (T k m : ℕ) :
    unitDigits T (k+m) = unitDigits T k ++ unitDigits (unitIter T k) m := by
  induction k generalizing T with
  | zero => simp [unitDigits, unitIter]
  | succ k ih => simp only [Nat.succ_add, unitDigits, ih, List.cons_append, unitIter_step_start]

theorem digits_data (σ : Convention) {T : ℕ} (hT : 1 ≤ T) (k : ℕ) :
    (unitDigits T k).length = k ∧
    (∀ d ∈ unitDigits T k, T < d) ∧ (unitDigits T k).Pairwise σ.rel ∧
    unit T = recipSum (unitDigits T k) + unit (unitIter T k) := by
  induction k generalizing T with
  | zero => simp [unitDigits, unitIter, recipSum]
  | succ k ih =>
    have hmul : T+1 ≤ T*(T+1) := Nat.le_mul_of_pos_left _ hT
    obtain ⟨hl, hmin, hord, hsum⟩ := ih (show 1 ≤ T*(T+1) by omega)
    simp only [unitDigits, List.length_cons, hl, List.mem_cons, List.pairwise_cons,
      forall_eq_or_imp, Nat.lt_add_one, true_and, ← unitIter_step_start]
    refine ⟨fun d hd => by have := hmin d hd; omega, ⟨?_, hord⟩, ?_⟩
    · intro d hd
      have := hmin d hd
      cases σ <;> simp only [Convention.rel] <;> omega
    · simp only [recipSum, List.map_cons, List.sum_cons] at hsum ⊢
      linarith [unit_sub_unit_succ hT]

theorem extension_data {σ q N p T} (hT : 1 ≤ T)
    (hp : Admissible σ q N p) (hstop : ∀ d ∈ p, d < T)
    (hsplit : q = recipSum p + unit T) (k : ℕ) :
    Admissible σ q (N+k) (p ++ unitDigits T k) ∧
      q = recipSum (p ++ unitDigits T k) + unit (unitIter T k) := by
  obtain ⟨hl, hmin, hord, hsum⟩ := digits_data σ hT k
  have hv : q = recipSum (p ++ unitDigits T k) + unit (unitIter T k) := by
    rw [recipSum_append]; linarith
  refine ⟨⟨by simp [hp.1, hl], ?_, List.pairwise_append.mpr ⟨hp.2.2.1, hord, ?_⟩, ?_⟩, hv⟩
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hp.2.1 _ h
    · have := hmin _ h; omega
  · intro x hx y hy
    have := hstop _ hx
    have := hmin _ hy
    cases σ <;> simp only [Convention.rel] <;> omega
  · have hpos : (0:ℚ) < unit (unitIter T k) :=
      one_div_pos.mpr (by exact_mod_cast (unitIter_pos hT k))
    linarith

/-- At a terminal optimum, the completion estimate rules out every strict
improvement, immediately in the weak convention and after the cutoff in the
strict one. -/
theorem best_extension_of_completion {σ q N p T} (hT : 2 ≤ T)
    (hp : Admissible σ q N p) (hstop : ∀ d ∈ p, d < T)
    (hsplit : q = recipSum p + unit T)
    (hcomplete : CompletionBound σ q (Payoff.value T / 2 ^ N))
    (k : ℕ) (hk : σ = .strict → max 4 (N + 1) ≤ k) :
    IsBest σ q (N+k) (p ++ unitDigits T k) := by
  let t : ℝ := unitIter T k
  have ht : 1 ≤ t := by dsimp only [t]; exact_mod_cast unitIter_pos (by omega : 1 ≤ T) k
  have hext := extension_data (by omega : 1 ≤ T) hp hstop hsplit k
  have hinv : Payoff.value T / 2 ^ N = Payoff.value t / 2^(N+k) := by
    dsimp only [t]
    rw [real_unitIter, Payoff.value_orbit (by exact_mod_cast (show 1 ≤ T by omega)), pow_add]
    field_simp
  refine ⟨hext.1, ?_⟩
  intro ds had
  by_contra! hbetter
  let h : ℝ := (q - recipSum ds : ℚ)
  have hpos : 0 < h := by dsimp only [h]; exact_mod_cast sub_pos.mpr had.2.2.2
  have he : h < 1 / t := by
    have hh : q - recipSum ds < unit (unitIter T k) := by linarith [hext.2]
    dsimp only [h, t]
    unfold unit at hh
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using (Rat.cast_lt (K := ℝ)).mpr hh
  have compare {r : ℕ} (hr : r ≤ N+k) {h' : ℝ}
      (hb : Payoff.value (1/h') / 2^(N+k-r) ≤ Payoff.value T / 2 ^ N) :
      (2:ℝ)^r * Payoff.value (1/h') ≤ Payoff.value t := by
    rw [hinv, show N+k = (N+k-r)+r by omega] at hb
    simp only [Nat.add_sub_cancel, pow_add] at hb
    have h₂ : (0:ℝ) < 2^(N+k-r) := by positivity
    field_simp at hb
    linarith
  cases σ with
  | weak =>
    obtain ⟨r, hr, h', hh, hd, hw, hb⟩ := hcomplete (N+k) ds had
      (he.le.trans (one_div_le_one_div_of_le (by norm_num) ht) |>.trans (by norm_num))
    obtain ⟨rfl, rfl⟩ := hw rfl
    have hh := compare hr hb
    simp only [pow_zero, one_mul] at hh
    exact he.not_ge (Payoff.no_better_weak ht hpos hh)
  | strict =>
    have hg := Payoff.tail_growth (t := (T:ℝ)) (by exact_mod_cast hT) N k (hk rfl)
    rw [← real_unitIter] at hg
    change 8 < t ∧ 2*((N+k:ℕ):ℝ)*Real.log 2 < Real.log t at hg
    have hscale := (Payoff.deletion_scaling hg.1 (le_refl (N+k)) hg.2).1
    have hpow : (0:ℝ) < 2^(N+k) := by positivity
    have hsize : (2:ℝ)^(N+k)*h ≤ 1 := by
      have hbound := (le_div_iff₀ hpow).mp hscale
      have := (lt_div_iff₀ (by linarith : 0 < t)).mp he
      nlinarith [mul_le_mul_of_nonneg_right (show (2:ℝ)^(N+k) ≤ t by linarith) hpos.le]
    obtain ⟨r, hr, h', hh, hd, _, hb⟩ := hcomplete (N+k) ds had hsize
    exact he.not_ge (Payoff.no_better_strict hg.1 hg.2 hr hh hd (compare hr hb))

/-- The final length and compatible prefix in the paper, with one explicit
uniform choice of cutoff for the strict convention. -/
theorem compatible_of_terminal_completion {σ q N p T} (hN : 1 ≤ N) (hT : 2 ≤ T)
    (hp : Admissible σ q N p) (hstop : ∀ d ∈ p, d < T)
    (hsplit : q = recipSum p + unit T)
    (hcomplete : CompletionBound σ q (Payoff.value T / 2 ^ N)) :
    ∃ (n U : ℕ) (ds : List ℕ), 1 ≤ n ∧ 1 ≤ U ∧
      q = recipSum ds + unit U ∧ IsBest σ q n ds ∧
      ∀ m, 1 ≤ m → IsBest σ q (n+m) (ds ++ greedyTuple σ (unit U) m) := by
  let k := match σ with | .weak => 0 | .strict => max 4 (N + 1)
  have hk : σ = .strict → max 4 (N + 1) ≤ k := by rintro rfl; exact le_rfl
  have h₁ : 1 ≤ T := by omega
  refine ⟨N+k, unitIter T k, p ++ unitDigits T k, by omega, unitIter_pos h₁ k,
    (extension_data h₁ hp hstop hsplit k).2,
    best_extension_of_completion hT hp hstop hsplit hcomplete k hk, ?_⟩
  intro m _
  rw [greedyTuple_unit σ (unitIter_pos h₁ k), List.append_assoc, ← digits_append,
    Nat.add_assoc]
  exact best_extension_of_completion hT hp hstop hsplit hcomplete (k+m)
    (fun hs => (hk hs).trans (Nat.le_add_right _ _))

end Egyptian
