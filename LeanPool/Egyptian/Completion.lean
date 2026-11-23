/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.TailOptimization
public import LeanPool.Egyptian.TerminalTuples
public import LeanPool.Egyptian.BellmanDrift

/-!
# Completion of a competing underapproximation

A strictly increasing terminal continuation of the remainder is extended until
its terminal denominator exceeds all original denominators. Sorting preserves
the reward. In the distinct convention an overlap is an original term smaller
than the current error, so deleting it permits a restart with the bound already
proved in `collision_restarts`.
-/

public section

namespace Egyptian.Control

theorem exists_initial_state {q : ℚ} (hq : 0 < q) :
    ∃ s : State, Valid s ∧ s.last = 0 ∧ (s.p : ℚ)/s.q = q := by
  have hp : 0 < q.num := Rat.num_pos.mpr hq
  have hcast : (q.num.natAbs : ℚ) = q.num := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hp.le]
  exact ⟨⟨q.num.natAbs, q.den, 0⟩, ⟨Int.natAbs_pos.mpr hp.ne', q.pos⟩, rfl,
    hcast ▸ q.num_div_den⟩

private theorem terminal_extend {s xs T} (hv : Valid s) (ht : Terminal .strict s xs T) :
    Terminal .strict s (xs ++ [T + 1]) (T * (T + 1)) := by
  let u := finish s xs
  have hstop : CanStop u T := ht.2
  obtain ⟨hT, hlast, hq⟩ := hstop
  have hp : 0 < u.p := (finish_valid hv ht.1).1
  have hlegal : Legal .strict u (T + 1) := by
    change u.q < u.p * (T + 1) ∧ 2 ≤ T + 1 ∧ u.last < T + 1
    rw [hq, Nat.mul_succ]
    exact ⟨by omega, by omega, by omega⟩
  have hlarge : T + 1 < T * (T + 1) := by
    simpa only [one_mul] using
      Nat.mul_lt_mul_of_pos_right (show 1 < T by omega) (Nat.succ_pos T)
  have hnew : CanStop (step u (T + 1)) (T * (T + 1)) := by
    refine ⟨by omega, hlarge, ?_⟩
    simp [step, hq, Nat.mul_succ, Nat.mul_assoc, Nat.mul_add]
  exact (terminal_append s xs [T + 1] (T * (T + 1))).mpr
    ⟨ht.1, ⟨hlegal, trivial⟩, hnew⟩

private theorem long_terminal {s : State} (hv : Valid s) (hi : Interior s)
    (hs : s.p ≤ s.q) (M : ℕ) :
    ∃ xs T, Terminal .strict s xs T ∧ M < T ∧
      Payoff.value (inverseRemainder s) ≤ (1/2 : ℝ)^xs.length * Payoff.value T := by
  induction M with
  | zero =>
    obtain ⟨xs,T,ht,hb,_⟩ := greedy_reward .strict s hv hi hs
    exact ⟨xs,T,ht,by have := ht.2.1; omega,hb⟩
  | succ M ih =>
    obtain ⟨xs,T,ht,hm,hb⟩ := ih
    have ht' := terminal_extend hv ht
    have hlarge := ht'.2.2.1
    rw [finish_append] at hlarge
    change T + 1 < T * (T + 1) at hlarge
    refine ⟨_,_,ht',by omega,?_⟩
    have hval := Payoff.value_phi (t := T) (by exact_mod_cast (show 1 ≤ T by omega))
    unfold Payoff.phi at hval
    simp only [List.length_append, List.length_singleton, pow_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, hval]
    linarith

private theorem entry_le_sum {d : ℕ} {ds : List ℕ} (hd : d ∈ ds) : unit d ≤ recipSum ds := by
  exact List.single_le_sum (fun x hx => by
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
    exact one_div_nonneg.mpr (Nat.cast_nonneg e)) _ (List.mem_map_of_mem hd)

/-- A successful sorted merge. The disjointness hypothesis only applies in the
strict convention. Both score contributions use the exact list lengths. -/
private theorem merge_score {σ s q bs cs U} (hv : Valid s) (hstart : s.last = 0)
    (hval : (s.p : ℚ) / s.q = q) (hbound : ∀ d ∈ bs, d < U)
    (hmin : ∀ d ∈ bs, 2 ≤ d) (hord : bs.Pairwise σ.rel)
    (hU : 2 ≤ U) (htail : ∀ d ∈ cs, 2 ≤ d ∧ d < U)
    (htord : cs.Pairwise (· < ·)) (hsum : q = recipSum bs + recipSum cs + unit U)
    (hdj : σ = .strict → bs.Disjoint cs) :
    (((1/2:ℝ)^(bs.length+cs.length) * Payoff.value U : ℝ) : EReal) ≤
      value σ (fun t => Payoff.value t) s := by
  let mixed := bs ++ cs
  let sorted := mixed.mergeSort (fun x y => decide (x ≤ y))
  have hp : sorted.Perm mixed := List.mergeSort_perm _ _
  have hle : sorted.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) mixed
  have hmix (d : ℕ) (hd : d ∈ sorted) : 2 ≤ d ∧ d < U := by
    rcases List.mem_append.mp (hp.mem_iff.mp hd) with hb | hc
    · exact ⟨hmin _ hb, hbound _ hb⟩
    · exact htail _ hc
  have hsorted : sorted.Pairwise σ.rel := by
    cases σ with
    | weak => exact hle
    | strict =>
      have hn : mixed.Nodup := List.nodup_append'.mpr
        ⟨hord.imp (by exact fun h => Nat.ne_of_lt h),
         htord.imp (by exact fun h => Nat.ne_of_lt h), hdj rfl⟩
      have hn' := hp.nodup_iff.mpr hn
      exact (hle.and hn').imp fun h => lt_of_le_of_ne h.1 h.2
  have he : recipSum sorted = recipSum bs + recipSum cs := by
    rw [← recipSum_append]; exact (hp.map unit).sum_eq
  have ht := terminal_of_tuple hv hU (by omega : s.last < U)
    (fun d hd => (hmix d hd).1)
    (σ := σ) (ds := sorted)
    (fun d hd => Convention.rel_of_lt (by have := (hmix d hd).1; omega))
    hsorted (fun d hd => (hmix d hd).2) (by linarith)
  have hlen : sorted.length = bs.length+cs.length := hp.length_eq.trans (List.length_append)
  simpa only [reward, hlen] using (reward_le_value (H := fun t => Payoff.value t) ht)

/-- The small-error completion lemma, under the supplied real upper bound C
for the initial Bellman supremum. For a maximizing terminal decomposition,
its own payoff is exactly such a bound. -/
theorem completion_bound_of_value_le {σ s q} {C : ℝ} (hv : Valid s) (hz : s.last = 0)
    (hval : (s.p : ℚ) / s.q = q)
    (hB : value σ (fun t => Payoff.value t) s ≤ (C : EReal)) :
    CompletionBound σ q C := by
  intro n ds had
  dsimp only
  intro hsmall
  let good := fun bs => Payoff.value (1 / ((q-recipSum bs : ℚ):ℝ)) / 2^bs.length ≤ C
  have run (bs : List ℕ) (hbs : bs.Sublist ds) (hp : 0 < q-recipSum bs)
      (h1 : q-recipSum bs ≤ 1) :
      good bs ∨ (σ = .strict ∧ ∃ d ∈ bs, unit d < q-recipSum bs) := by
    let h := q-recipSum bs
    obtain ⟨z,hzv,hz0,hzq⟩ := exists_initial_state hp
    have hq0 : (0:ℚ) < z.q := by exact_mod_cast hzv.2
    have hs : z.p ≤ z.q := by
      have := (div_le_iff₀ hq0).mp (hzq.trans_le h1)
      simpa only [one_mul, Nat.cast_le] using this
    have hi : Interior z := by unfold Interior; rw [hz0, zero_mul]; exact hzv.2
    obtain ⟨cs,U,ht,hU,hgain⟩ := long_terminal hzv hi hs bs.sum
    obtain ⟨ha,hup,hend⟩ := terminal_to_tuple hzv ht
    have hrep : h = recipSum cs + unit U := hzq.symm.trans hend
    have hu : 0 < unit U := one_div_pos.mpr (by exact_mod_cast (show 0 < U by
      have := ht.2.1; omega))
    by_cases hc : σ = .strict ∧ ¬ bs.Disjoint cs
    · right
      refine ⟨hc.1, ?_⟩
      obtain ⟨d,hd1,hd2⟩ : ∃ d ∈ bs, d ∈ cs := by
        by_contra! hh
        exact hc.2 (fun {d} hb hd => hh d hb hd)
      exact ⟨d,hd1,(entry_le_sum hd2).trans_lt (by change recipSum cs < h; linarith)⟩
    · left
      have hm := merge_score hv hz hval (fun d hd => (List.le_sum_of_mem hd).trans_lt hU)
        (fun d hd => had.2.1 d (hbs.subset hd)) (had.2.2.1.sublist hbs)
        ht.2.1 (fun d hd => ⟨ha.2.1 d hd, hup d hd⟩) ha.2.2.1
        (by dsimp [h] at hrep; linarith : q = recipSum bs + recipSum cs + unit U)
        (fun he => by by_contra hn; exact hc ⟨he,hn⟩)
      have hb := EReal.coe_le_coe_iff.mp (hm.trans hB)
      have hinv : inverseRemainder z = 1 / (h:ℝ) := by
        change (z.q:ℝ) / z.p = _
        rw [show h = (z.p:ℚ)/z.q from hzq.symm]
        simp [one_div]
      rw [hinv] at hgain
      change Payoff.value (1/(h:ℝ)) / 2^bs.length ≤ C
      rw [pow_add] at hb
      calc
        _ ≤ ((1/2:ℝ)^cs.length * Payoff.value U) / 2^bs.length :=
          div_le_div_of_nonneg_right hgain (by positivity)
        _ = (1/2:ℝ)^bs.length * (1/2:ℝ)^cs.length * Payoff.value U := by
          rw [div_eq_mul_inv, ← inv_pow, ← one_div]; ring
        _ ≤ _ := hb
  have hpos := sub_pos.mpr had.2.2.2
  cases σ with
  | weak =>
    have hsm : q-recipSum ds ≤ 1 := by exact_mod_cast hsmall
    have hgood := (run ds (.refl _) hpos hsm).resolve_right (by simp)
    refine ⟨0, by omega, _, ?_, by simp, fun _ => ⟨rfl,rfl⟩, ?_⟩
    · exact_mod_cast hpos
    · simpa only [Nat.sub_zero, ← had.1] using hgood
  | strict =>
    have hsm : (2:ℚ)^ds.length * (q-recipSum ds) ≤ 1 := by
      rw [had.1]; exact_mod_cast hsmall
    obtain ⟨bs,hbs,hgood,hd⟩ := collision_restarts good ds hpos hsm
      (fun b hb hp h1 => (run b hb hp h1).imp_right And.right)
    have hlen := hbs.length_le
    have hsum : recipSum bs ≤ recipSum ds := by
      apply (hbs.map unit).sum_le_sum
      intro v hv
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp hv
      unfold unit; positivity
    refine ⟨n-bs.length, by omega, ((q-recipSum bs : ℚ):ℝ), ?_, ?_, by simp, ?_⟩
    · exact_mod_cast (show 0 < q-recipSum bs by linarith)
    · rw [← had.1]; exact_mod_cast hd
    · have he : n-(n-bs.length) = bs.length := by have := had.1; omega
      simpa only [he] using hgood

end Egyptian.Control
