/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.BalancedKingman.Vitali

/-!
# Rokhlin's lemma

The classical Kakutani–Rokhlin tower theorem: for an ergodic invertible measure-preserving
transformation on a non-atomic probability space, and any height `n` and error `ε > 0`, there
is a measurable "tower base" `B` such that `B, σB, …, σ^(n-1)B` are pairwise disjoint and their
union misses less than `ε` of the space.

**Proved as a corollary of `backwardVitali`**, which is Rudolph's own route (his Theorem 3.10,
which he flags as "a very unusual and in fact difficult proof, in that it uses the much deeper
backward Vitali lemma"). Backward Vitali itself uses no towers, so there is no circularity.

`Ω` carries a `[StandardBorelSpace Ω]` hypothesis, matching the paper's blanket "Lebesgue
probability space" assumption (`human/proof_met.tex`, e.g. the standing hypotheses of
`thm:kingman`/`lem:bvit`). This is not just decoration: Mathlib's `NullSingletonClass` alone
(singletons are null) is *strictly weaker* than the classical "no atoms" property (every
positive-measure set splits into two positive-measure pieces) on a general measurable space --
see the `TODO` note in `Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass`, which
states the implication only goes one way. `StandardBorelSpace` is exactly the extra structure
that closes the gap, via a measurable embedding into `ℝ` (`ProofMet.NonAtomic` proves the
splitting fact on `ℝ` itself, from continuity of measures along `Iic`-cumulative functions). -/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The points lying on a finite `σ`-orbit. -/
def periodicPts (σ : Ω ≃ᵐ Ω) : Set Ω := ⋃ p : ℕ, {x | (⇑σ)^[p + 1] x = x}

theorem measurableSet_periodicPts (σ : Ω ≃ᵐ Ω) : MeasurableSet (periodicPts σ) :=
  MeasurableSet.iUnion fun p => measurableSet_eq_fun (σ.measurable.iterate (p + 1)) measurable_id

theorem measure_periodicPts (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (⇑σ) μ) : μ (periodicPts σ) = 0 :=
  measure_iUnion_null fun p => periodic_null μ σ hσ (by omega : 1 ≤ p + 1)

omit [StandardBorelSpace Ω] in
/-- Off the periodic points, the two-sided orbit map `t ↦ σ^t x` is injective. -/
theorem zIter_inj_of_not_periodic (σ : Ω ≃ᵐ Ω) {x : Ω} (hx : x ∉ periodicPts σ) {a b : ℤ}
    (h : zIter σ a x = zIter σ b x) : a = b := by
  have key : ∀ a b : ℤ, a < b → zIter σ a x = zIter σ b x → False := by
    intro a b hab h
    have h2 : zIter σ (b - a) x = x := by
      have := congrArg (zIter σ (-a)) h
      rw [← zIter_add, ← zIter_add, show -a + a = 0 by ring, zIter_zero_apply] at this
      rw [show b - a = -a + b by ring]; exact this.symm
    obtain ⟨p, hp⟩ : ∃ p : ℕ, b - a = ((p + 1 : ℕ) : ℤ) := ⟨(b - a - 1).toNat, by omega⟩
    rw [hp, zIter_natCast] at h2
    exact hx (Set.mem_iUnion.2 ⟨p, h2⟩)
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (key a b hab h).elim
  · exact hab
  · exact (key b a hab h.symm).elim

/-- **Rokhlin's lemma** (Kakutani–Rokhlin tower with small error). For an ergodic invertible
measure-preserving transformation on a non-atomic probability space, every height `n ≥ 1` and
every `ε > 0` admit a measurable tower base `B`: `B, σB, …, σ^(n-1)B` are pairwise disjoint,
and their union covers all but `< ε` of the space.

Non-atomicity is what "aperiodic" buys in the general statement -- it rules out the degenerate
case of `Ω` being (up to null sets) a single finite periodic orbit, where no positive-measure
set can avoid returning to itself within `n` steps for large `n`.

**Proof**, from `backwardVitali` with the constant half-widths `n(k+K)`, `1/(2nK+1) ≤ ε/2`:
discard the null set of periodic points from the window centres `A`, leaving `A'`; slice each
window `[-N, N]` (`N` a multiple of `n`) into `2N/n` height-`n` blocks, and let `B` be the union of
their bottom points. Two levels `σ^i B`, `σ^j B` meeting would put one point at two offsets of a
single window, and off the periodic set the offsets are then equal, so `i ≡ j (mod n)`. Each
window loses only its top point to the slicing; those points have total measure `≤ μ A'`, and
`μ A' ≤ 1/(2nK+1)` because the `2nK+1` translates of `A'` are pairwise disjoint. -/
theorem rokhlin_lemma (μ : Measure Ω) [IsProbabilityMeasure μ] [MeasureTheory.NullSingletonClass μ]
    (σ : Ω ≃ᵐ Ω) (hσ : Ergodic σ μ) (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : Set Ω, MeasurableSet B ∧
      (∀ i < n, ∀ j < n, i ≠ j → Disjoint (σ^[i] '' B) (σ^[j] '' B)) ∧
      ENNReal.ofReal (1 - ε) < μ (⋃ i ∈ Finset.range n, σ^[i] '' B) := by
  classical
  -- reduce to `ε ≤ 1`
  wlog hε1 : ε ≤ 1 generalizing ε
  · obtain ⟨B, hB, hd, hc⟩ := this 1 one_pos le_rfl
    refine ⟨B, hB, hd, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by linarith)) hc⟩
  -- the window half-widths `n (k + K)`, with `1/(2nK+1) ≤ ε/2`
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / ε)
  have hKε : (1 : ℝ) ≤ (2 * n * K + 1) * (ε / 2) := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : 2 < (K : ℝ) * ε := by rwa [div_lt_iff₀ hε] at hK
    nlinarith
  have hjm : ∀ k, Measurable fun _ : Ω => n * (k + K) := fun _ => measurable_const
  have hjtop : ∀ ω : Ω, Tendsto (fun k => (fun (k : ℕ) (_ : Ω) => n * (k + K)) k ω) atTop atTop :=
    fun _ => tendsto_atTop_mono (fun k => show k ≤ n * (k + K) by nlinarith) tendsto_id
  obtain ⟨A, jω, hA, hjω, hjform, hdisj, hcov⟩ :=
    backwardVitali μ σ hσ (ε / 2) (by positivity) (fun k _ => n * (k + K)) hjm hjtop
  set A' := A \ periodicPts σ with hA'def
  have hA' : MeasurableSet A' := hA.diff (measurableSet_periodicPts σ)
  have hA'A : A' ⊆ A := Set.sdiff_subset
  have hnp : ∀ ω ∈ A', ω ∉ periodicPts σ := fun ω h => h.2
  have hjK : ∀ ω ∈ A', n * K ≤ jω ω := by
    intro ω hω
    obtain ⟨k, hk⟩ := hjform ω (hA'A hω)
    rw [hk]; exact Nat.mul_le_mul_left _ (by omega)
  have hjdiv : ∀ ω ∈ A', n * (jω ω / n) = jω ω := by
    intro ω hω
    obtain ⟨k, hk⟩ := hjform ω (hA'A hω)
    rw [hk, Nat.mul_div_cancel_left _ (by omega)]
  set win : Ω → Set Ω := fun ω => (fun i => zIter σ i ω) '' Set.Icc (-(jω ω : ℤ)) (jω ω)
    with hwin
  -- two points of `A'` whose windows share a point at the given offsets coincide, as do offsets
  have hsame : ∀ ω ∈ A', ∀ ω' ∈ A', ∀ a b : ℤ, a ∈ Set.Icc (-(jω ω : ℤ)) (jω ω) →
      b ∈ Set.Icc (-(jω ω' : ℤ)) (jω ω') → zIter σ a ω = zIter σ b ω' → ω = ω' ∧ a = b := by
    intro ω hω ω' hω' a b ha hb hab
    by_cases hne : ω = ω'
    · subst hne; exact ⟨rfl, zIter_inj_of_not_periodic σ (hnp ω hω) hab⟩
    · exact ((Set.disjoint_left.1 (hdisj (hA'A hω) (hA'A hω') hne) ⟨a, ha, rfl⟩)
        ⟨b, hb, hab.symm⟩).elim
  -- the pieces of `A'` by window width
  set Ap : ℕ → Set Ω := fun N => A' ∩ jω ⁻¹' {N} with hApdef
  have hAp : ∀ N, MeasurableSet (Ap N) := fun N => hA'.inter (hjω (measurableSet_singleton N))
  set B : Set Ω := ⋃ N : ℕ, ⋃ t ∈ Finset.range (2 * (N / n)),
    zIter σ ((t * n : ℕ) - (N : ℤ)) '' Ap N with hBdef
  have hB : MeasurableSet B :=
    MeasurableSet.iUnion fun N => MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun _ =>
      measurableSet_zIter_image σ _ (hAp N)
  -- membership in `σ^i B`, as an offset in a window
  have hmemB : ∀ i < n, ∀ y ∈ σ^[i] '' B, ∃ ω ∈ A', ∃ t < 2 * (jω ω / n),
      y = zIter σ ((i : ℤ) + (t * n : ℕ) - (jω ω : ℤ)) ω ∧
      ((i : ℤ) + (t * n : ℕ) - (jω ω : ℤ)) ∈ Set.Icc (-(jω ω : ℤ)) (jω ω) := by
    intro i hi y hy
    obtain ⟨z, hz, rfl⟩ := hy
    simp only [hBdef, Set.mem_iUnion, Finset.mem_range] at hz
    obtain ⟨N, t, ht, ω, ⟨hω, hωN⟩, rfl⟩ := hz
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hωN
    subst hωN
    refine ⟨ω, hω, t, ht, ?_, ?_⟩
    · rw [← zIter_natCast, ← zIter_add]; congr 1; ring
    · have h1 := hjdiv ω hω
      have h2 : t * n + i < 2 * jω ω := by
        have : (t + 1) * n ≤ 2 * (jω ω / n) * n := Nat.mul_le_mul_right _ (by omega)
        nlinarith
      constructor <;> push_cast <;> omega
  refine ⟨B, hB, ?_, ?_⟩
  · -- disjointness of the levels
    intro i hi j hj hij
    rw [Set.disjoint_left]
    intro y hyi hyj
    obtain ⟨ω, hω, t, ht, rfl, hwi⟩ := hmemB i hi y hyi
    obtain ⟨ω', hω', t', ht', hy', hwj⟩ := hmemB j hj _ hyj
    obtain ⟨rfl, hoff⟩ := hsame ω hω ω' hω' _ _ hwi hwj hy'
    have : (i + t * n) % n = (j + t' * n) % n := by
      congr 1; push_cast at hoff; omega
    simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
    exact hij this
  · -- the covering estimate
    set U := ⋃ i ∈ Finset.range n, σ^[i] '' B with hUdef
    set L : Set Ω := ⋃ N : ℕ, zIter σ (N : ℤ) '' Ap N with hLdef
    set P' : Set Ω := ⋃ t : ℤ, zIter σ t '' periodicPts σ with hP'def
    have hP' : μ P' = 0 := measure_iUnion_null fun t => by
      rw [measure_zIter_image σ hσ t (measurableSet_periodicPts σ), measure_periodicPts μ σ hσ]
    have hsub : (⋃ ω ∈ A, win ω) ⊆ (U ∪ L) ∪ P' := by
      intro x hx
      simp only [hwin, Set.mem_iUnion] at hx
      obtain ⟨ω, hωA, s, hs, rfl⟩ := hx
      by_cases hp : ω ∈ periodicPts σ
      · exact Or.inr (Set.mem_iUnion.2 ⟨s, ω, hp, rfl⟩)
      have hω : ω ∈ A' := ⟨hωA, hp⟩
      refine Or.inl ?_
      rcases eq_or_lt_of_le hs.2 with hsN | hsN
      · refine Or.inr (Set.mem_iUnion.2 ⟨jω ω, ω, ⟨hω, rfl⟩, ?_⟩)
        rw [hsN]
      · refine Or.inl ?_
        set N := jω ω with hN
        set u : ℕ := (s + N).toNat with hu
        have hus : (u : ℤ) = s + N := by rw [hu]; exact Int.toNat_of_nonneg (by linarith [hs.1])
        have hu2 : u < 2 * (N / n) * n := by
          have := hjdiv ω hω
          have : (u : ℤ) < 2 * N := by rw [hus]; linarith
          have : u < 2 * N := by exact_mod_cast this
          nlinarith
        have hmd := Nat.mod_add_div' u n
        have hr : u % n < n := Nat.mod_lt _ (by omega)
        have ht : u / n < 2 * (N / n) := (Nat.div_lt_iff_lt_mul (by omega)).2 hu2
        simp only [hUdef, Set.mem_iUnion, Finset.mem_range]
        refine ⟨u % n, hr, zIter σ (((u / n) * n : ℕ) - (N : ℤ)) ω, ?_, ?_⟩
        · simp only [hBdef, Set.mem_iUnion, Finset.mem_range]
          exact ⟨N, u / n, ht, ω, ⟨hω, rfl⟩, rfl⟩
        · rw [← zIter_natCast, ← zIter_add]
          congr 1
          have : ((u % n : ℕ) : ℤ) + ((u / n * n : ℕ) : ℤ) = (u : ℤ) := by exact_mod_cast hmd
          linarith
    have hL : μ L ≤ μ A' := by
      calc μ L ≤ ∑' N : ℕ, μ (zIter σ (N : ℤ) '' Ap N) := measure_iUnion_le _
        _ = ∑' N : ℕ, μ (Ap N) := by
          congr 1; funext N; exact measure_zIter_image σ hσ _ (hAp N)
        _ = μ (⋃ N, Ap N) := by
          rw [measure_iUnion ?_ hAp]
          intro N M hNM
          change Disjoint (Ap N) (Ap M)
          rw [Set.disjoint_left]
          rintro x ⟨_, hx⟩ ⟨_, hx'⟩
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
          exact hNM (hx.symm.trans hx')
        _ = μ A' := by
          congr 1; ext x
          simp only [hApdef, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
            Set.mem_singleton_iff]
          exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩
    have hsmall : μ A' ≤ ENNReal.ofReal (ε / 2) := by
      have heq := measure_iUnion_zIter_window_eq (μ := μ) σ hσ (n * K) hA' (by
        intro a ha b hb hab
        rw [Set.disjoint_left]
        rintro x ⟨ω, hω, rfl⟩ ⟨ω', hω', hx⟩
        have hK1 := hjK ω hω
        have hK2 := hjK ω' hω'
        have hK1' : ((n * K : ℕ) : ℤ) ≤ jω ω := by exact_mod_cast hK1
        have hK2' : ((n * K : ℕ) : ℤ) ≤ jω ω' := by exact_mod_cast hK2
        obtain ⟨-, h⟩ := hsame ω' hω' ω hω b a ⟨by linarith [hb.1], by linarith [hb.2]⟩
          ⟨by linarith [ha.1], by linarith [ha.2]⟩ hx
        exact hab h.symm)
      have hle : (2 * ((n * K : ℕ) : ENNReal) + 1) * μ A' ≤ 1 := heq ▸ prob_le_one
      have hne : μ A' ≠ ⊤ := measure_ne_top μ _
      rw [← ENNReal.ofReal_toReal hne]
      refine ENNReal.ofReal_le_ofReal ?_
      have hr := ENNReal.toReal_mono ENNReal.one_ne_top hle
      rw [ENNReal.toReal_mul] at hr
      have hc : (2 * ((n * K : ℕ) : ENNReal) + 1).toReal = 2 * (n : ℝ) * K + 1 := by
        rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) (ENNReal.natCast_ne_top _)) (by simp)]
        simp [ENNReal.toReal_mul]; ring
      rw [hc] at hr
      simp only [ENNReal.toReal_one] at hr
      have h0 : 0 ≤ (μ A').toReal := ENNReal.toReal_nonneg
      nlinarith
    have hbig : ENNReal.ofReal (1 - ε / 2) < μ U + ENNReal.ofReal (ε / 2) :=
      calc ENNReal.ofReal (1 - ε / 2) < μ (⋃ ω ∈ A, win ω) := hcov
        _ ≤ μ ((U ∪ L) ∪ P') := measure_mono hsub
        _ ≤ μ (U ∪ L) + μ P' := measure_union_le _ _
        _ ≤ μ U + μ L := by rw [hP', add_zero]; exact measure_union_le _ _
        _ ≤ μ U + ENNReal.ofReal (ε / 2) := by gcongr; exact hL.trans hsmall
    by_contra hU
    rw [not_lt] at hU
    have hsplit : ENNReal.ofReal (1 - ε / 2) = ENNReal.ofReal (1 - ε) + ENNReal.ofReal (ε / 2) := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring
    rw [hsplit] at hbig
    exact absurd hbig (not_lt.2 (by gcongr))

end MultiplicativeErgodic
