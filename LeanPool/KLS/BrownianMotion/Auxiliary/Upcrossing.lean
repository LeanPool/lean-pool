/-
Copyright (c) 2026 Rohit Manokaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: Lean/Mathlib v4.35.0 replacements
-- of deprecated names (identifier-only); see vendor/port.patch.
module

public import Mathlib.Probability.Martingale.Upcrossing

/-! # Upcrossings and path limits -/


@[expose] public section

namespace MeasureTheory

variable {ι Ω β : Type*} {mΩ : MeasurableSpace Ω}
  {f g : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ} {ω : Ω}

@[simp]
lemma hittingBtwn_self [ConditionallyCompletePartialOrderInf ι]
    (f : ι → Ω → β) (s : Set β) (n : ι) (ω : Ω) :
    hittingBtwn f s n n ω = n := by
  rw [hittingBtwn]
  simp only [Set.Icc_self, Set.mem_singleton_iff, exists_eq_left, ite_eq_right_iff]
  intro h
  simp [h]

/-- `hittingBtwn` only depends on the hitting predicate. -/
lemma hittingBtwn_congr {s : Set ℝ}
    (h : ∀ i ω, f i ω ∈ s ↔ g i ω ∈ s) (n m : ℕ) :
    hittingBtwn f s n m = hittingBtwn g s n m := by
  ext
  unfold hittingBtwn
  congr <;> ext <;> simp [h]

/-- Upper crossing times only depend on the position of the process relative to `a` and `b`. -/
lemma upperCrossingTime_congr
    (hIic : ∀ i ω, f i ω ≤ a ↔ g i ω ≤ a) (hIci : ∀ i ω, b ≤ f i ω ↔ b ≤ g i ω) (n : ℕ) :
    upperCrossingTime a b f N n = upperCrossingTime a b g N n := by
  have hIic' : ∀ i ω, f i ω ∈ Set.Iic a ↔ g i ω ∈ Set.Iic a := hIic
  have hIci' : ∀ i ω, f i ω ∈ Set.Ici b ↔ g i ω ∈ Set.Ici b := hIci
  induction n with
  | zero => rfl
  | succ n ih =>
    ext ω
    rw [upperCrossingTime_succ_eq, upperCrossingTime_succ_eq, lowerCrossingTime,
      lowerCrossingTime, ih, hittingBtwn_congr hIic', hittingBtwn_congr hIci']

/-- Lower crossing times only depend on the position of the process relative to `a` and `b`. -/
lemma lowerCrossingTime_congr
    (hIic : ∀ i ω, f i ω ≤ a ↔ g i ω ≤ a) (hIci : ∀ i ω, b ≤ f i ω ↔ b ≤ g i ω) (n : ℕ) :
    lowerCrossingTime a b f N n = lowerCrossingTime a b g N n := by
  ext ω
  rw [lowerCrossingTime, lowerCrossingTime, upperCrossingTime_congr hIic hIci,
    hittingBtwn_congr hIic]

lemma upcrossingStrat_congr
    (hIic : ∀ i ω, f i ω ≤ a ↔ g i ω ≤ a) (hIci : ∀ i ω, b ≤ f i ω ↔ b ≤ g i ω) (n : ℕ) :
    upcrossingStrat a b f N n = upcrossingStrat a b g N n := by
  ext ω
  simp_rw [upcrossingStrat, upperCrossingTime_congr hIic hIci, lowerCrossingTime_congr hIic hIci]

lemma upcrossingsBefore_congr
    (hIic : ∀ i ω, f i ω ≤ a ↔ g i ω ≤ a) (hIci : ∀ i ω, b ≤ f i ω ↔ b ≤ g i ω) :
    upcrossingsBefore a b f N ω = upcrossingsBefore a b g N ω := by
  simp_rw [upcrossingsBefore, upperCrossingTime_congr hIic hIci]

/-- `upcrossingStrat` takes only the values `0` and `1`. -/
lemma upcrossingStrat_eq_zero_or_one (a b : ℝ) (f : ℕ → Ω → ℝ) (N n : ℕ) (ω : Ω) :
    upcrossingStrat a b f N n ω = 0 ∨ upcrossingStrat a b f N n ω = 1 := by
  classical
  rw [upcrossingStrat, ← Finset.indicator_biUnion_apply]
  · rw [Set.indicator_apply]
    split_ifs <;> simp
  intro i _ j _ hij
  simp only [Set.Ico_disjoint_Ico]
  rcases lt_or_gt_of_ne hij with hij' | hij'
  · rw [min_eq_left (upperCrossingTime_mono (Nat.succ_le_succ hij'.le) :
      upperCrossingTime a b f N _ ω ≤ upperCrossingTime a b f N _ ω),
      max_eq_right (lowerCrossingTime_mono hij'.le :
        lowerCrossingTime a b f N _ _ ≤ lowerCrossingTime _ _ _ _ _ _)]
    exact le_trans upperCrossingTime_le_lowerCrossingTime
      (lowerCrossingTime_mono (Nat.succ_le_of_lt hij'))
  · rw [min_eq_right (upperCrossingTime_mono (Nat.succ_le_succ hij'.le) :
      upperCrossingTime a b f N _ ω ≤ upperCrossingTime a b f N _ ω),
      max_eq_left (lowerCrossingTime_mono hij'.le :
        lowerCrossingTime a b f N _ _ ≤ lowerCrossingTime _ _ _ _ _ _)]
    exact upperCrossingTime_le_lowerCrossingTime.trans
      (lowerCrossingTime_mono (Nat.succ_le_of_lt hij'))

/-- Pathwise upcrossing inequality with correction term: unlike
`MeasureTheory.mul_upcrossingsBefore_le`, this requires no assumption `a ≤ f N ω`, at the price
of the extra term `max (a - f N ω) 0`. -/
lemma mul_upcrossingsBefore_le_sum_add_posPart (hab : a < b) :
    (b - a) * upcrossingsBefore a b f N ω ≤
      (∑ k ∈ Finset.range N, upcrossingStrat a b f N k ω * (f (k + 1) - f k) ω) + (a - f N ω)⁺ := by
  rcases N with _ | M
  · simp [posPart, upcrossingsBefore_zero]
  let g : ℕ → Ω → ℝ := fun k ω' ↦ if k = M + 1 then max (f k ω') a else f k ω'
  have hIic i ω' : g i ω' ≤ a ↔ f i ω' ≤ a := by simp [g]; grind
  have hIci i ω' : b ≤ g i ω' ↔ b ≤ f i ω' := by simp [g]; grind
  have hga : a ≤ g (M + 1) ω := by simp [g]
  have key : (b - a) * upcrossingsBefore a b g (M + 1) ω ≤
      ∑ k ∈ Finset.range (M + 1), upcrossingStrat a b g (M + 1) k ω * (g (k + 1) - g k) ω :=
    mul_upcrossingsBefore_le (f := g) (N := M + 1) (ω := ω) hga hab
  simp_rw [upcrossingsBefore_congr hIic hIci, upcrossingStrat_congr hIic hIci] at key
  refine key.trans ?_
  rw [Finset.sum_range_succ, Finset.sum_range_succ
    (f := fun k ↦ upcrossingStrat a b f (M + 1) k ω * (f (k + 1) - f k) ω)]
  have hsum k (hk : k ∈ Finset.range M) :
      upcrossingStrat a b f (M + 1) k ω * (g (k + 1) - g k) ω
        = upcrossingStrat a b f (M + 1) k ω * (f (k + 1) - f k) ω := by simp [g]; grind
  rw [Finset.sum_congr rfl hsum, add_assoc]
  gcongr
  have hgM : g M = f M := by simp [g]
  have hgM1 : g (M + 1) ω = f (M + 1) ω + (a - f (M + 1) ω)⁺ := by simp [g, posPart]; grind
  rw [Pi.sub_apply, hgM, hgM1]
  have h11 : upcrossingStrat a b f (M + 1) M ω ≤ 1 := upcrossingStrat_le_one
  calc upcrossingStrat a b f (M + 1) M ω * (f (M + 1) ω + (a - f (M + 1) ω)⁺ - f M ω)
  _ = upcrossingStrat a b f (M + 1) M ω * (f (M + 1) - f M) ω
      + upcrossingStrat a b f (M + 1) M ω * (a - f (M + 1) ω)⁺ := by rw [Pi.sub_apply]; ring
  _ ≤ upcrossingStrat a b f (M + 1) M ω * (f (M + 1) - f M) ω + 1 * (a - f (M + 1) ω)⁺ := by
    gcongr
  _ = upcrossingStrat a b f (M + 1) M ω * (f (M + 1) - f M) ω + (a - f (M + 1) ω)⁺ := by ring

/-- Non-strict variant of `MeasureTheory.upcrossingsBefore_lt_of_exists_upcrossing`: since the
lower crossing hits `Set.Iic a` and the upper crossing hits `Set.Ici b`, it suffices that the
levels are *reached* (`f N₁ ω ≤ a` and `b ≤ f N₂ ω`) rather than strictly crossed. The Mathlib
proof already only uses the non-strict forms internally. -/
lemma upcrossingsBefore_lt_of_exists_upcrossing' (hab : a < b) {N₁ N₂ : ℕ} (hN₁ : N ≤ N₁)
    (hN₁' : f N₁ ω ≤ a) (hN₂ : N₁ ≤ N₂) (hN₂' : b ≤ f N₂ ω) :
    upcrossingsBefore a b f N ω < upcrossingsBefore a b f (N₂ + 1) ω := by
  refine lt_of_lt_of_le (Nat.lt_succ_self _) (le_csSup (upperCrossingTime_lt_bddAbove hab) ?_)
  rw [Set.mem_ofPred_eq, upperCrossingTime_succ_eq, hittingBtwn_lt_iff _ le_rfl]
  refine ⟨N₂, ⟨?_, Nat.lt_succ_self _⟩, hN₂'⟩
  rw [lowerCrossingTime, hittingBtwn_le_iff_of_lt _ (Nat.lt_succ_self _)]
  refine ⟨N₁, ⟨le_trans ?_ hN₁, hN₂⟩, hN₁'⟩
  by_cases! hN : 0 < N
  · have : upperCrossingTime a b f N (upcrossingsBefore a b f N ω) ω < N :=
      Nat.sSup_mem (upperCrossingTime_lt_nonempty hN) (upperCrossingTime_lt_bddAbove hab)
    rw [upperCrossingTime_eq_upperCrossingTime_of_lt (hN₁.trans (hN₂.trans <| Nat.le_succ _)) this]
    exact this.le
  · rw [Nat.le_zero] at hN
    rw [hN, upcrossingsBefore_zero, upperCrossingTime_zero, Pi.bot_apply, bot_eq_zero']

/-- Alternations force upcrossings: if there are `m` pairs of (strictly increasing) times below
`N` at which `f` is alternately at most `a` and at least `b`, then `f` has at least
`m` upcrossings of `[a, b]` before `N`. -/
lemma le_upcrossingsBefore_of_alternating (hab : a < b) {m : ℕ} {c : ℕ → ℕ}
    (hmono : ∀ i, i + 1 < 2 * m → c i < c (i + 1)) (hN : ∀ i < 2 * m, c i < N)
    (ha : ∀ i < m, f (c (2 * i)) ω ≤ a) (hb : ∀ i < m, b ≤ f (c (2 * i + 1)) ω) :
    m ≤ upcrossingsBefore a b f N ω := by
  rcases m with _ | m
  · simp
  have key i : i < m + 1 → i + 1 ≤ upcrossingsBefore a b f (c (2 * i + 1) + 1) ω := by
    induction i with
    | zero =>
      intro h0
      have := upcrossingsBefore_lt_of_exists_upcrossing' (f := f) (ω := ω) (N := 0) hab
        (by lia) (ha 0 h0) (hmono 0 (by lia)).le (hb 0 h0)
      lia
    | succ i ih =>
      intro hi
      have h2 := upcrossingsBefore_lt_of_exists_upcrossing' (f := f) (ω := ω)
        (N := c (2 * i + 1) + 1) hab (hmono (2 * i + 1) (by lia)) (ha (i + 1) hi)
        (hmono (2 * (i + 1)) (by lia)).le (hb (i + 1) hi)
      lia
  refine (key m (by lia)).trans ?_
  exact upcrossingsBefore_mono (f := f) hab (hN (2 * m + 1) (by lia)) ω

/-- Converse of `le_upcrossingsBefore_of_alternating`: if `f` has at least `m` upcrossings of
`[a, b]` before `N`, then there is a strictly increasing sequence of `2 * m` times below `N` at
which `f` is alternately at most `a` (at even positions) and at least `b` (at odd positions). The
times are the lower/upper crossing times. -/
lemma exists_alternating_of_le_upcrossingsBefore (hab : a < b) {m : ℕ}
    (hm : m ≤ upcrossingsBefore a b f N ω) :
    ∃ c : ℕ → ℕ, (∀ i, i + 1 < 2 * m → c i < c (i + 1)) ∧ (∀ i < 2 * m, c i < N)
      ∧ (∀ i < m, f (c (2 * i)) ω ≤ a) ∧ (∀ i < m, b ≤ f (c (2 * i + 1)) ω) := by
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · exact ⟨fun _ ↦ 0, by simp, by simp, by simp, by simp⟩
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · rw [upcrossingsBefore_zero] at hm; lia
    · exact h
  have hLlt : ∀ n, n < m → lowerCrossingTime a b f N n ω < N := fun n hn ↦
    lowerCrossingTime_lt_of_lt_upcrossingsBefore hNpos hab (hn.trans_le hm)
  have hUlt : ∀ n, n ≤ m → upperCrossingTime a b f N n ω < N := fun n hn ↦
    upperCrossingTime_lt_of_le_upcrossingsBefore hNpos hab (hn.trans hm)
  set idx : ℕ → ℕ :=
    fun i ↦ if Even i then lowerCrossingTime a b f N (i / 2) ω
      else upperCrossingTime a b f N (i / 2 + 1) ω with hidx
  have he : ∀ j, idx (2 * j) = lowerCrossingTime a b f N j ω := by
    intro j
    simp only [hidx]
    rw [ite_eq_left (even_two.mul_right j), show 2 * j / 2 = j from by omega]
  have ho : ∀ j, idx (2 * j + 1) = upperCrossingTime a b f N (j + 1) ω := by
    intro j
    simp only [hidx]
    rw [ite_eq_right (Nat.not_even_iff_odd.mpr ⟨j, rfl⟩ : ¬ Even (2 * j + 1)),
      show (2 * j + 1) / 2 = j from by omega]
  refine ⟨idx, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases Nat.even_or_odd i with hev | hodd
    · have hev2 : i % 2 = 0 := Nat.even_iff.mp hev
      have e1 : idx i = lowerCrossingTime a b f N (i / 2) ω := by
        simp only [hidx]; rw [ite_eq_left hev]
      have e2 : idx (i + 1) = upperCrossingTime a b f N (i / 2 + 1) ω := by
        simp only [hidx]
        rw [ite_eq_right (Nat.not_even_iff_odd.mpr hev.add_one : ¬ Even (i + 1)),
          show (i + 1) / 2 = i / 2 from by omega]
      rw [e1, e2]
      exact lowerCrossingTime_lt_upperCrossingTime hab (ne_of_lt (hUlt _ (by omega)))
    · have hodd2 : i % 2 = 1 := Nat.odd_iff.mp hodd
      have e1 : idx i = upperCrossingTime a b f N (i / 2 + 1) ω := by
        simp only [hidx]; rw [ite_eq_right (Nat.not_even_iff_odd.mpr hodd)]
      have e2 : idx (i + 1) = lowerCrossingTime a b f N (i / 2 + 1) ω := by
        simp only [hidx]
        rw [ite_eq_left (hodd.add_one : Even (i + 1)), show (i + 1) / 2 = i / 2 + 1 from by omega]
      rw [e1, e2]
      exact upperCrossingTime_lt_lowerCrossingTime hab (ne_of_lt (hLlt _ (by omega)))
  · intro i hi
    rcases Nat.even_or_odd i with hev | hodd
    · have e1 : idx i = lowerCrossingTime a b f N (i / 2) ω := by
        simp only [hidx]; rw [ite_eq_left hev]
      rw [e1]; exact hLlt _ (by omega)
    · have e1 : idx i = upperCrossingTime a b f N (i / 2 + 1) ω := by
        simp only [hidx]; rw [ite_eq_right (Nat.not_even_iff_odd.mpr hodd)]
      rw [e1]; exact hUlt _ (by omega)
  · intro i hi
    rw [he i]
    exact stoppedValue_lowerCrossingTime (ne_of_lt (hLlt i hi))
  · intro i hi
    rw [ho i]
    exact stoppedValue_upperCrossingTime (ne_of_lt (hUlt (i + 1) hi))

end MeasureTheory
