/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.BalancedKingman.Walk

/-!
# Gap bounds and gap sums

The two majorants `gapMaj`, `gapCount` and the uncovered set, and the telescoping estimates that
turn gap values and gap lengths each into a single Birkhoff sum.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter

open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
/-- The gap's left endpoint in the walk between the selected windows' endpoint sets. -/
noncomputable abbrev windowGapStart (σ : Ω ≃ᵐ Ω) (jω : Ω → ℕ) (A : Set Ω) : ℕ → Ω → ℕ :=
  bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A)

/-- The gap's right endpoint in the walk between the selected windows' endpoint sets. -/
noncomputable abbrev windowGapEnd (σ : Ω ≃ᵐ Ω) (jω : Ω → ℕ) (A : Set Ω) : ℕ → Ω → ℕ :=
  aWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A)

/-- The block counter specialized to the selected windows' endpoint sets. -/
noncomputable abbrev windowBlockCount (σ : Ω ≃ᵐ Ω) (jω : Ω → ℕ) (A : Set Ω) : ℕ → Ω → ℕ :=
  blockCount (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A)

section GapBounds
variable {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ} {ω : Ω}

local notation "gapStart" => bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A)
local notation "gapEnd" => aWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A)
local notation "blockTotal" => blockCount (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A)

/-- The `(i+1)`-st gap has positive length: its left end is a right endpoint, which is not a left
endpoint, and the orbit does return to `Λ₋`. -/
theorem one_le_gap_length
    (hdisj : A.PairwiseDisjoint fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hpos : ∀ ω' ∈ A, 1 ≤ jω ω')
    (hinj : ∀ ω' ∈ A, Function.Injective fun i : ℤ => zIter σ i ω')
    (hrecp : ∀ m : ℕ, ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ (rightEnd σ jω '' A))
    (hrecm : ∀ m : ℕ, ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ (leftEnd σ jω '' A)) (i : ℕ) :
    1 ≤ gapEnd (i + 1) ω - gapStart (i + 1) ω := by
  have hbmem : (σ : Ω → Ω)^[gapStart (i + 1) ω] ω ∈ (rightEnd σ jω '' A) :=
    bWalk_succ_mem_of_recur hrecp i
  have hnotm : (σ : Ω → Ω)^[gapStart (i + 1) ω] ω ∉ (leftEnd σ jω '' A) :=
    fun hc => Set.disjoint_left.mp (disjoint_leftEnd_rightEnd hdisj hpos hinj) hc hbmem
  have hlen : gapEnd (i + 1) ω - gapStart (i + 1) ω =
      hitTime (σ : Ω → Ω) (leftEnd σ jω '' A) ((σ : Ω → Ω)^[gapStart (i + 1) ω] ω) := by
    rw [aWalk, rMinus]; omega
  rw [hlen]
  rcases Nat.eq_zero_or_pos (hitTime (σ : Ω → Ω) (leftEnd σ jω '' A)
    ((σ : Ω → Ω)^[gapStart (i + 1) ω] ω)) with h0 | h
  · exact absurd (by simpa [h0] using hitTime_spec (hrecm (gapStart (i + 1) ω))) hnotm
  · exact h

/-- Every point of the `(i+1)`-st gap is either uncovered or a right endpoint. -/
theorem gap_point_mem_shifted
    (hdisj : A.PairwiseDisjoint fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hinj : ∀ ω' ∈ A, Function.Injective fun i : ℤ => zIter σ i ω')
    (hrecp : ∀ m : ℕ, ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ (rightEnd σ jω '' A)) (i : ℕ)
    {k : ℕ} (hk : k < gapEnd (i + 1) ω - gapStart (i + 1) ω) :
    (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[gapStart (i + 1) ω] ω) ∈ uncovered σ jω A ∨
      (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[gapStart (i + 1) ω] ω) ∈ (rightEnd σ jω '' A) := by
  have hbmem : (σ : Ω → Ω)^[gapStart (i + 1) ω] ω ∈ (rightEnd σ jω '' A) :=
    bWalk_succ_mem_of_recur hrecp i
  have hlen : gapEnd (i + 1) ω - gapStart (i + 1) ω =
      rMinus (σ : Ω → Ω) (leftEnd σ jω '' A) ((σ : Ω → Ω)^[gapStart (i + 1) ω] ω) := by
    rw [aWalk]; omega
  rw [hlen] at hk
  have h := gap_point_mem hdisj hinj hbmem hk
  rwa [Nat.add_comm, Function.iterate_add_apply] at h

/-- **Gap lengths are counted by `gapCount`.** -/
theorem gap_length_le_birkhoffSum
    (hdisj : A.PairwiseDisjoint fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hinj : ∀ ω' ∈ A, Function.Injective fun i : ℤ => zIter σ i ω')
    (hrecp : ∀ m : ℕ, ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ (rightEnd σ jω '' A)) (i : ℕ) :
    ((gapEnd (i + 1) ω - gapStart (i + 1) ω : ℕ) : ℝ)
      ≤ birkhoffSum (σ : Ω → Ω) (gapCount σ jω A) (gapEnd (i + 1) ω - gapStart (i + 1) ω)
        ((σ : Ω → Ω)^[gapStart (i + 1) ω] ω) := by
  have hterm : ∀ k ∈ Finset.range (gapEnd (i + 1) ω - gapStart (i + 1) ω),
      (1 : ℝ) ≤ gapCount σ jω A ((σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[gapStart (i + 1) ω] ω)) :=
    fun k hk =>
    one_le_gapCount (gap_point_mem_shifted hdisj hinj hrecp i (Finset.mem_range.mp hk))
  have hcard := Finset.card_nsmul_le_sum (Finset.range (gapEnd (i + 1) ω - gapStart (i + 1) ω))
    (fun k => gapCount σ jω A ((σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[gapStart (i + 1) ω] ω))) (1 : ℝ) hterm
  rw [Finset.card_range, nsmul_eq_mul, mul_one] at hcard
  exact hcard

/-- **Gap values are dominated by `gapMaj`.** -/
theorem gap_value_le_birkhoffSum {f : ℕ → Ω → ℝ} (hf : SubadditiveFamily (σ : Ω → Ω) f)
    (hdisj : A.PairwiseDisjoint fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hpos : ∀ ω' ∈ A, 1 ≤ jω ω')
    (hinj : ∀ ω' ∈ A, Function.Injective fun i : ℤ => zIter σ i ω')
    (hrecp : ∀ m : ℕ, ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ (rightEnd σ jω '' A))
    (hrecm : ∀ m : ℕ, ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ (leftEnd σ jω '' A)) (i : ℕ) :
    f (gapEnd (i + 1) ω - gapStart (i + 1) ω) ((σ : Ω → Ω)^[gapStart (i + 1) ω] ω)
      ≤ birkhoffSum (σ : Ω → Ω) (gapMaj σ jω A f) (gapEnd (i + 1) ω - gapStart (i + 1) ω)
        ((σ : Ω → Ω)^[gapStart (i + 1) ω] ω) := by
  have hm1 : 1 ≤ gapEnd (i + 1) ω - gapStart (i + 1) ω :=
    one_le_gap_length hdisj hpos hinj hrecp hrecm i
  have hsub := gap_le_sum hf (gapStart (i + 1) ω) (gapEnd (i + 1) ω - gapStart (i + 1) ω) hm1 ω
  refine le_trans hsub ?_
  rw [birkhoffSum]
  refine Finset.sum_le_sum (fun k hk => ?_)
  have hpt := gap_point_mem_shifted hdisj hinj hrecp i (Finset.mem_range.mp hk)
  have hrw : (σ : Ω → Ω)^[gapStart (i + 1) ω + k] ω =
      (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[gapStart (i + 1) ω] ω) := by
    rw [Nat.add_comm, Function.iterate_add_apply]
  rw [hrw]
  exact le_gapMaj hpt

end GapBounds

section GapSums
variable {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ} {ω : Ω}

local notation "gapStart" => bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A)
local notation "gapEnd" => aWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A)
local notation "blockTotal" => blockCount (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A)

/-- The initial gap `[0, a₀)` is what `firstGap` measures, once at least one block is complete. -/
theorem firstGap_eq (hbn : blockTotal n ω ≠ 0) :
    gapEnd (0) ω - gapStart (0) ω = firstGap σ jω A n ω := by
  have hb0 : gapStart (0) ω = 0 := rfl
  have hle : gapStart (blockTotal n ω) ω ≤ n := bWalk_blockCount_le _ _ _ _ _
  have h1 : gapEnd (0) ω < gapStart (1) ω := aWalk_lt_bWalk_succ _ _ _ 0 ω
  have h2 : gapStart (1) ω ≤ gapStart (blockTotal n ω) ω :=
    (bWalk_strictMono (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) ω).monotone (by omega)
  rw [firstGap]
  omega

/-- **Total gap length.** The initial gap plus a `gapCount` Birkhoff sum. -/
theorem gap_length_sum_le
    (hdisj : A.PairwiseDisjoint fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hinj : ∀ ω' ∈ A, Function.Injective fun i : ℤ => zIter σ i ω')
    (hrecp : ∀ m : ℕ, ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ (rightEnd σ jω '' A)) (n : ℕ) :
    ∑ i ∈ Finset.range (blockTotal n ω), ((gapEnd (i) ω - gapStart (i) ω : ℕ) : ℝ)
      ≤ (firstGap σ jω A n ω : ℝ) + birkhoffSum (σ : Ω → Ω) (gapCount σ jω A) n ω := by
  have hnn : (0 : ℝ) ≤ birkhoffSum (σ : Ω → Ω) (gapCount σ jω A) n ω :=
    Finset.sum_nonneg (fun k _ => gapCount_nonneg σ jω A _)
  have hle : gapStart (blockTotal n ω) ω ≤ n := bWalk_blockCount_le _ _ _ _ _
  rcases Nat.eq_zero_or_pos (blockTotal n ω) with h0 | hp
  · rw [h0]
    simp only [Finset.range_zero, Finset.sum_empty]
    have : (0 : ℝ) ≤ (firstGap σ jω A n ω : ℝ) := Nat.cast_nonneg _
    linarith
  · obtain ⟨t', ht'⟩ : ∃ t', blockTotal n ω = t' + 1 := ⟨blockTotal n ω - 1, by omega⟩
    have hfirst : gapEnd (0) ω - gapStart (0) ω = firstGap σ jω A n ω := firstGap_eq (by omega)
    have hrest : ∑ i ∈ Finset.range t', ((gapEnd (i + 1) ω - gapStart (i + 1) ω : ℕ) : ℝ)
        ≤ birkhoffSum (σ : Ω → Ω) (gapCount σ jω A) n ω := by
      refine sum_shifted_gaps_le (gapCount_nonneg σ jω A) ω _ t'
        (fun i _ => gap_length_le_birkhoffSum hdisj hinj hrecp i) n ?_
      rw [← ht']; exact hle
    rw [ht', Finset.sum_range_succ', hfirst]
    linarith

/-- **Total gap value.** The initial gap, bounded by `|f₁|`, plus a `gapMaj` Birkhoff sum. -/
theorem gap_value_sum_le {f : ℕ → Ω → ℝ} (hf : SubadditiveFamily (σ : Ω → Ω) f)
    (hdisj : A.PairwiseDisjoint fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hpos : ∀ ω' ∈ A, 1 ≤ jω ω')
    (hinj : ∀ ω' ∈ A, Function.Injective fun i : ℤ => zIter σ i ω')
    (hrecp : ∀ m : ℕ, ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ (rightEnd σ jω '' A))
    (hrecm : ∀ m : ℕ, ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ (leftEnd σ jω '' A)) (n : ℕ) :
    ∑ i ∈ Finset.range (blockTotal n ω), f (gapEnd (i) ω - gapStart (i) ω) ((σ : Ω →
      Ω)^[gapStart (i) ω] ω)
      ≤ f 0 ω + birkhoffSum (σ : Ω → Ω) (fun x => |f 1 x|) (firstGap σ jω A n ω) ω
        + birkhoffSum (σ : Ω → Ω) (gapMaj σ jω A f) n ω := by
  have hf0 : 0 ≤ f 0 ω := by
    have h := hf.2 0 0 ω
    simp only [Nat.add_zero, Function.iterate_zero, id_eq] at h
    linarith
  have hSnn : (0 : ℝ) ≤ birkhoffSum (σ : Ω → Ω) (gapMaj σ jω A f) n ω :=
    Finset.sum_nonneg (fun k _ => gapMaj_nonneg σ jω A f _)
  have hTnn : ∀ m : ℕ, (0 : ℝ) ≤ birkhoffSum (σ : Ω → Ω) (fun x => |f 1 x|) m ω :=
    fun m => Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hle : gapStart (blockTotal n ω) ω ≤ n := bWalk_blockCount_le _ _ _ _ _
  rcases Nat.eq_zero_or_pos (blockTotal n ω) with h0 | hp
  · rw [h0]
    simp only [Finset.range_zero, Finset.sum_empty]
    have := hTnn (firstGap σ jω A n ω)
    linarith
  · obtain ⟨t', ht'⟩ : ∃ t', blockTotal n ω = t' + 1 := ⟨blockTotal n ω - 1, by omega⟩
    have hfirst : gapEnd (0) ω - gapStart (0) ω = firstGap σ jω A n ω := firstGap_eq (by omega)
    have hb0 : gapStart (0) ω = 0 := rfl
    -- the initial gap
    have hzero : f (gapEnd (0) ω - gapStart (0) ω) ((σ : Ω → Ω)^[gapStart (0) ω] ω)
        ≤ f 0 ω + birkhoffSum (σ : Ω → Ω) (fun x => |f 1 x|) (firstGap σ jω A n ω) ω := by
      rcases Nat.eq_zero_or_pos (gapEnd (0) ω) with ha0 | ha1
      · have : gapEnd (0) ω - gapStart (0) ω = 0 := by omega
        rw [this, hb0]
        simp only [Function.iterate_zero, id_eq]
        have := hTnn (firstGap σ jω A n ω)
        linarith
      · rw [hfirst]
        have hsub := gap_le_sum hf (gapStart (0) ω) (firstGap σ jω A n ω) (by omega) ω
        have hterm : ∑ k ∈ Finset.range (firstGap σ jω A n ω), f 1 ((σ : Ω → Ω)^[gapStart (0) ω
          + k] ω)
            ≤ birkhoffSum (σ : Ω → Ω) (fun x => |f 1 x|) (firstGap σ jω A n ω) ω := by
          rw [birkhoffSum]
          refine Finset.sum_le_sum (fun k _ => ?_)
          rw [show gapStart (0) ω + k = k from by omega]
          exact le_abs_self _
        linarith
    have hrest : ∑ i ∈ Finset.range t', f (gapEnd (i + 1) ω - gapStart (i + 1) ω) ((σ : Ω →
      Ω)^[gapStart (i + 1) ω] ω)
        ≤ birkhoffSum (σ : Ω → Ω) (gapMaj σ jω A f) n ω := by
      refine sum_shifted_gaps_le (gapMaj_nonneg σ jω A f) ω _ t'
        (fun i _ => gap_value_le_birkhoffSum hf hdisj hpos hinj hrecp hrecm i) n ?_
      rw [← ht']; exact hle
    rw [ht', Finset.sum_range_succ']
    linarith

end GapSums

/-- **The paper's pointwise decomposition of `f_n`,** assembled.

`[0, n)` splits as the initial gap, then alternating good blocks and gaps, then a trailing
segment. Good blocks contribute at most `q ·` their length; gaps contribute at most a `gapMaj`
Birkhoff sum; the initial and trailing segments contribute `|f₁|` sums over `[0, a₀)` and
`[b_{t_n}, n)`. Replacing the total good length by `n` costs `|q|` times the total gap length,
which is itself bounded by a `gapCount` Birkhoff sum. Every term on the right is either a fixed
integrable function's Birkhoff sum or an index which the cutoff estimates make small. -/
theorem covering_pointwise {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ} {f : ℕ → Ω → ℝ} {q : ℝ}
    (hf : SubadditiveFamily (σ : Ω → Ω) f)
    (hdisj : A.PairwiseDisjoint fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hgood : ∀ ω' ∈ A, 1 ≤ jω ω' ∧
      f (2 * jω ω') (zIter σ (-(jω ω' : ℤ)) ω') < 2 * (jω ω') * q)
    (hinj : ∀ ω' ∈ A, Function.Injective fun i : ℤ => zIter σ i ω') {ω : Ω}
    (hrecp : ∀ m : ℕ, ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ (rightEnd σ jω '' A))
    (hrecm : ∀ m : ℕ, ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ (leftEnd σ jω '' A)) (n : ℕ) :
    f n ω ≤ 2 * f 0 ω
      + birkhoffSum (σ : Ω → Ω) (fun x => |f 1 x|) (firstGap σ jω A n ω) ω
      + (birkhoffSum (σ : Ω → Ω) (fun x => |f 1 x|) n ω
          - birkhoffSum (σ : Ω → Ω) (fun x => |f 1 x|) (lastBlock σ jω A n ω) ω)
      + birkhoffSum (σ : Ω → Ω) (gapMaj σ jω A f) n ω
      + q * n
      + |q| * (((n - lastBlock σ jω A n ω : ℕ) : ℝ) + ((firstGap σ jω A n ω : ℕ) : ℝ)
          + birkhoffSum (σ : Ω → Ω) (gapCount σ jω A) n ω) := by
  let gapStart := windowGapStart σ jω A
  let gapEnd := windowGapEnd σ jω A
  let blockTotal := windowBlockCount σ jω A
  classical
  have hpos : ∀ ω' ∈ A, 1 ≤ jω ω' := fun ω' h => (hgood ω' h).1
  have hf0 : 0 ≤ f 0 ω := by
    have h := hf.2 0 0 ω
    simp only [Nat.add_zero, Function.iterate_zero, id_eq] at h
    linarith
  have hbn : gapStart (blockTotal n ω) ω ≤ n := bWalk_blockCount_le _ _ _ _ _
  have hlast : lastBlock σ jω A n ω = gapStart (blockTotal n ω) ω := rfl
  rw [hlast]
  -- **Trailing segment.**
  have hM1 : f n ω ≤ (birkhoffSum (σ : Ω → Ω) (fun x => |f 1 x|) n ω - birkhoffSum (σ : Ω → Ω)
    (fun x => |f 1 x|) (gapStart (blockTotal n ω) ω) ω)
      + f (gapStart (blockTotal n ω) ω) ω := by
    rcases eq_or_lt_of_le hbn with heq | hlt
    · rw [heq]; simp
    · have hsp := le_split_at_bWalk hf (gapStart (blockTotal n ω) ω) n hbn ω
      have hb2 := boundary_le_sum hf (gapStart (blockTotal n ω) ω) n hlt ω
      have habs : ∑ k ∈ Finset.range (n - gapStart (blockTotal n ω) ω), f 1 ((σ : Ω →
        Ω)^[gapStart (blockTotal n ω) ω + k] ω)
          ≤ birkhoffSum (σ : Ω → Ω) (fun x => |f 1 x|) (n - gapStart (blockTotal n ω) ω) ((σ :
            Ω → Ω)^[gapStart (blockTotal n ω) ω] ω) := by
        rw [birkhoffSum]
        refine Finset.sum_le_sum (fun k _ => ?_)
        have hit : (σ : Ω → Ω)^[gapStart (blockTotal n ω) ω + k] ω = (σ : Ω → Ω)^[k] ((σ : Ω →
          Ω)^[gapStart (blockTotal n ω) ω] ω) := by
          rw [Nat.add_comm, Function.iterate_add_apply]
        rw [hit]
        exact le_abs_self _
      have hshift := birkhoffSum_shift_eq (σ := (σ : Ω → Ω)) (fun x => |f 1 x|) (gapStart
        (blockTotal n ω) ω) (n - gapStart (blockTotal n ω) ω) ω
      rw [Nat.add_sub_cancel' hbn] at hshift
      linarith
  -- **Good blocks are cheap.**
  have hgoodH : ∀ i < blockTotal n ω,
      f (gapStart (i + 1) ω - gapEnd (i) ω) ((σ : Ω → Ω)^[gapEnd (i) ω] ω) ≤ q * ((gapStart (i
        + 1) ω - gapEnd (i) ω : ℕ) : ℝ) := by
    intro i _
    have hmemm : (σ : Ω → Ω)^[gapEnd (i) ω] ω ∈ (leftEnd σ jω '' A) := by
      have h := hitTime_spec (hrecm (gapStart (i) ω))
      rw [← Function.iterate_add_apply] at h
      rw [show gapEnd (i) ω =
      hitTime (σ : Ω → Ω) (leftEnd σ jω '' A) ((σ : Ω → Ω)^[gapStart (i) ω] ω) + gapStart (i) ω
        from by
        simp only [gapEnd, windowGapEnd, gapStart, windowGapStart, aWalk, rMinus]; omega]
      exact h
    have hnot : (σ : Ω → Ω)^[gapEnd (i) ω] ω ∉ (rightEnd σ jω '' A) :=
      fun hc => Set.disjoint_left.mp (disjoint_leftEnd_rightEnd hdisj hpos hinj) hmemm hc
    have hlen : gapStart (i + 1) ω - gapEnd (i) ω = hitTime (σ : Ω → Ω) (rightEnd σ jω '' A)
      ((σ : Ω → Ω)^[gapEnd (i) ω] ω) :=
      goodlen_eq_hitTime i (hrecp (gapEnd (i) ω)) hnot
    rw [hlen]
    exact good_block_value hdisj hgood hinj hmemm
  have hM2 := chained_bound hf (leftEnd σ jω '' A) (rightEnd σ jω '' A) (blockTotal n ω) ω
    (fun i => f (gapEnd (i) ω - gapStart (i) ω) ((σ : Ω → Ω)^[gapStart (i) ω] ω))
    (fun i => q * ((gapStart (i + 1) ω - gapEnd (i) ω : ℕ) : ℝ)) (fun i _ => le_refl _) hgoodH
  rw [Finset.sum_add_distrib] at hM2
  -- **Gap values.**
  have hM4 := gap_value_sum_le hf hdisj hpos hinj hrecp hrecm n
  -- **Gap lengths, and the price of replacing the good length by `n`.**
  have hM5 := gap_length_sum_le hdisj hinj hrecp n
  have hwalkR : (∑ i ∈ Finset.range (blockTotal n ω), ((gapEnd (i) ω - gapStart (i) ω : ℕ) : ℝ))
      + (∑ i ∈ Finset.range (blockTotal n ω), ((gapStart (i + 1) ω - gapEnd (i) ω : ℕ) : ℝ)) =
        ((gapStart (blockTotal n ω) ω : ℕ) : ℝ) := by
    have h : ((∑ i ∈ Finset.range (blockTotal n ω),
        ((gapEnd (i) ω - gapStart (i) ω) + (gapStart (i + 1) ω - gapEnd (i) ω)) : ℕ) : ℝ) =
          ((gapStart (blockTotal n ω) ω : ℕ) : ℝ) := by
      rw [sum_walk_lengths]
    rw [Nat.cast_sum] at h
    simp only [Nat.cast_add] at h
    rw [Finset.sum_add_distrib] at h
    exact h
  have hGnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range (blockTotal n ω), ((gapEnd (i) ω - gapStart (i) ω :
    ℕ) : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hbnR : ((gapStart (blockTotal n ω) ω : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hbn
  have hbeta : ((n - gapStart (blockTotal n ω) ω : ℕ) : ℝ) = (n : ℝ) - ((gapStart (blockTotal n
    ω) ω : ℕ) : ℝ) := by
    rw [Nat.cast_sub hbn]
  have hLn : (∑ i ∈ Finset.range (blockTotal n ω), ((gapStart (i + 1) ω - gapEnd (i) ω : ℕ) :
    ℝ)) ≤ (n : ℝ) := by linarith
  have hnL : (n : ℝ) - (∑ i ∈ Finset.range (blockTotal n ω), ((gapStart (i + 1) ω - gapEnd (i)
    ω : ℕ) : ℝ))
      ≤ ((n - gapStart (blockTotal n ω) ω : ℕ) : ℝ) + ((firstGap σ jω A n ω : ℕ) : ℝ)
        + birkhoffSum (σ : Ω → Ω) (gapCount σ jω A) n ω := by
    rw [hbeta]; linarith
  have hqsum : ∑ i ∈ Finset.range (blockTotal n ω), q * ((gapStart (i + 1) ω - gapEnd (i) ω :
    ℕ) : ℝ)
      = q * ∑ i ∈ Finset.range (blockTotal n ω), ((gapStart (i + 1) ω - gapEnd (i) ω : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
  have hq : q * (∑ i ∈ Finset.range (blockTotal n ω), ((gapStart (i + 1) ω - gapEnd (i) ω : ℕ) : ℝ))
      ≤ q * (n : ℝ) + |q| * (((n - gapStart (blockTotal n ω) ω : ℕ) : ℝ) + ((firstGap σ jω A n
        ω : ℕ) : ℝ)
          + birkhoffSum (σ : Ω → Ω) (gapCount σ jω A) n ω) := by
    have hle : q * ((∑ i ∈ Finset.range (blockTotal n ω), ((gapStart (i + 1) ω - gapEnd (i) ω :
      ℕ) : ℝ)) - (n : ℝ))
        ≤ |q * ((∑ i ∈ Finset.range (blockTotal n ω), ((gapStart (i + 1) ω - gapEnd (i) ω : ℕ)
          : ℝ)) - (n : ℝ))| :=
      le_abs_self _
    have heq : |q * ((∑ i ∈ Finset.range (blockTotal n ω), ((gapStart (i + 1) ω - gapEnd (i) ω
      : ℕ) : ℝ)) - (n : ℝ))|
        = |q| * ((n : ℝ) - ∑ i ∈ Finset.range (blockTotal n ω), ((gapStart (i + 1) ω - gapEnd
          (i) ω : ℕ) : ℝ)) := by
      rw [abs_mul,
        abs_of_nonpos (by linarith : (∑ i ∈ Finset.range (blockTotal n ω),
        ((gapStart (i + 1) ω - gapEnd (i) ω : ℕ) : ℝ)) - (n : ℝ) ≤ 0)]
      ring
    rw [heq] at hle
    have hmul := mul_le_mul_of_nonneg_left hnL (abs_nonneg q)
    nlinarith [hle, hmul]
  rw [hqsum] at hM2
  linarith

/-- **The union of the windows is measurable.** It is an uncountable union, but recasting
membership in forward terms (`mem_iUnion_windows_iff`) turns it into a *countable* union of
Lusin–Souslin images: one for each forward offset `m` from a left endpoint. -/
theorem measurableSet_iUnion_windows [StandardBorelSpace Ω] {σ : Ω ≃ᵐ Ω} {A : Set Ω}
    (hA : MeasurableSet A) {jω : Ω → ℕ} (hj : Measurable jω)
    (hdisj : A.PairwiseDisjoint fun ω => (fun i => zIter σ i ω) '' Set.Icc (-(jω ω : ℤ)) (jω ω)) :
    MeasurableSet (⋃ ω' ∈ A, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω')) := by
  classical
  have hEq : (⋃ ω' ∈ A, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω'))
      = ⋃ m : ℕ, zIter σ (m : ℤ) '' (leftEnd σ jω '' (A ∩ {ω' | m ≤ 2 * jω ω'})) := by
    ext x
    rw [mem_iUnion_windows_iff]
    constructor
    · rintro ⟨ω', hω', m, hm, rfl⟩
      exact Set.mem_iUnion.mpr ⟨m, ⟨leftEnd σ jω ω', ⟨ω', ⟨hω', hm⟩, rfl⟩, by rw [zIter_natCast]⟩⟩
    · intro hx
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
      obtain ⟨y, ⟨ω', ⟨hω'A, hω'm⟩, rfl⟩, rfl⟩ := hm
      exact ⟨ω', hω'A, m, hω'm, by rw [zIter_natCast]⟩
  rw [hEq]
  refine MeasurableSet.iUnion (fun m => measurableSet_zIter_image σ (m : ℤ) ?_)
  refine measurableSet_leftEnd_image
    (hA.inter (measurableSet_le measurable_const (measurable_const.mul hj))) hj
    (hdisj.subset Set.inter_subset_left)

/-- If the centres carry positive measure then so does any set of endpoints they are orbit
translates of. Used to know `μ Λ± > 0`, which is what makes the hitting times a.e. finite. -/
theorem measure_ne_zero_of_endpoints {μ : Measure Ω} (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (⇑σ) μ)
    {A Λ : Set Ω} (hΛm : MeasurableSet Λ) (e : Ω → Ω) (k : Ω → ℤ)
    (he : ∀ ω ∈ A, e ω ∈ Λ ∧ zIter σ (k ω) (e ω) = ω) (hA : μ A ≠ 0) : μ Λ ≠ 0 := by
  intro h0
  refine hA (measure_mono_null (s := A) (t := ⋃ m : ℤ, zIter σ m '' Λ) (fun ω hω => ?_) ?_)
  · obtain ⟨hmem, heq⟩ := he ω hω
    exact Set.mem_iUnion.mpr ⟨k ω, ⟨e ω, hmem, heq⟩⟩
  · refine measure_iUnion_null (fun m : ℤ => ?_)
    rw [measure_zIter_image σ hσ m hΛm]
    exact h0

omit [MeasurableSpace Ω] in
theorem aWalk_zero (σ : Ω → Ω) (Λm Λp : Set Ω) (ω : Ω) :
    aWalk σ Λm Λp 0 ω = rMinus σ Λm ω := by
  rw [aWalk]
  simp [bWalk]

/-- Measurability of the initial-gap length. -/
theorem measurable_firstGap {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ}
    (hm : MeasurableSet (leftEnd σ jω '' A)) (n : ℕ) :
    Measurable (fun ω => firstGap σ jω A n ω) := by
  have h : (fun ω => firstGap σ jω A n ω)
      = fun ω => min (rMinus (σ : Ω → Ω) (leftEnd σ jω '' A) ω) n := by
    funext ω; rw [firstGap, aWalk_zero]
  rw [h]
  exact (measurable_rMinus σ.measurable hm).min measurable_const

/-- Measurability of `b_{t_n}`: the walk position is a measurable function of `ω` for each fixed
index, the index `t_n` is measurable, and `t_n ≤ n`, so the composite is a countable case split. -/
theorem measurable_lastBlock {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ}
    (hm : MeasurableSet (leftEnd σ jω '' A)) (hp : MeasurableSet (rightEnd σ jω '' A)) (n : ℕ) :
    Measurable (fun ω => lastBlock σ jω A n ω) := by
  classical
  refine measurable_to_countable' (fun c => ?_)
  have hEq : (fun ω => lastBlock σ jω A n ω) ⁻¹' {c}
      = ⋃ t ∈ Finset.range (n + 1),
        ({ω | windowBlockCount σ jω A n ω = t}
          ∩ {ω | windowGapStart σ jω A t ω = c}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Finset.mem_range, exists_prop]
    constructor
    · intro h
      exact ⟨windowBlockCount σ jω A n ω,
        Nat.lt_succ_of_le (Nat.findGreatest_le n), rfl, h⟩
    · rintro ⟨t, _, ht, hb⟩
      change blockCount (σ : Ω → Ω) (leftEnd σ jω '' A)
        (rightEnd σ jω '' A) n ω = t at ht
      rw [lastBlock, ht]
      exact hb
  rw [hEq]
  refine MeasurableSet.biUnion (Finset.range (n + 1)).countable_toSet (fun t _ => ?_)
  exact (measurable_blockCount σ.measurable hm hp n (measurableSet_singleton t)).inter
    (measurable_bWalk σ.measurable hm hp t (measurableSet_singleton c))

/-- The cutoff exceptional set: the initial gap or the trailing segment is longer than `M`.
Its measure is small *uniformly in `n`* — that is the point of `sub_bWalk_le_hitBack`. -/
def badSet (σ : Ω ≃ᵐ Ω) (jω : Ω → ℕ) (A : Set Ω) (M n : ℕ) : Set Ω :=
  {ω | M ≤ firstGap σ jω A n ω} ∪ {ω | lastBlock σ jω A n ω + M ≤ n}

theorem measurableSet_badSet {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ}
    (hm : MeasurableSet (leftEnd σ jω '' A)) (hp : MeasurableSet (rightEnd σ jω '' A))
    (M n : ℕ) : MeasurableSet (badSet σ jω A M n) :=
  (measurableSet_le measurable_const (measurable_firstGap hm n)).union
    (measurableSet_le ((measurable_lastBlock hm hp n).add_const M) measurable_const)

/-- **The decomposition, with every `ω`-dependent index removed.** Off `badSet` the two end
segments sit in `[0, M)` and `[n - M, n)`; on `badSet` everything is absorbed into the indicator
terms, whose integrals are small because `badSet` has small measure. -/
theorem covering_pointwise_clean {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ} {f : ℕ → Ω → ℝ} {q : ℝ}
    (hf : SubadditiveFamily (σ : Ω → Ω) f)
    (hdisj : A.PairwiseDisjoint fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hgood : ∀ ω' ∈ A, 1 ≤ jω ω' ∧
      f (2 * jω ω') (zIter σ (-(jω ω' : ℤ)) ω') < 2 * (jω ω') * q)
    (hinj : ∀ ω' ∈ A, Function.Injective fun i : ℤ => zIter σ i ω') {ω : Ω}
    (hrecp : ∀ m : ℕ, ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ rightEnd σ jω '' A)
    (hrecm : ∀ m : ℕ, ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ leftEnd σ jω '' A)
    {M n : ℕ} (hMn : M ≤ n) :
    f n ω ≤ 2 * f 0 ω
      + birkhoffSum (σ : Ω → Ω) (fun x => |f 1 x|) M ω
      + birkhoffSum (σ : Ω → Ω) (fun x => |f 1 x|) M ((σ : Ω → Ω)^[n - M] ω)
      + 2 * (badSet σ jω A M n).indicator
          (fun x => birkhoffSum (σ : Ω → Ω) (fun y => |f 1 y|) n x) ω
      + birkhoffSum (σ : Ω → Ω) (gapMaj σ jω A f) n ω
      + q * n
      + |q| * (2 * M + 2 * n * (badSet σ jω A M n).indicator (fun _ => (1 : ℝ)) ω
          + birkhoffSum (σ : Ω → Ω) (gapCount σ jω A) n ω) := by
  classical
  have hcov := covering_pointwise hf hdisj hgood hinj hrecp hrecm n
  have hTnn : ∀ (k : ℕ) (x : Ω), (0 : ℝ) ≤ birkhoffSum (σ : Ω → Ω) (fun y => |f 1 y|) k x :=
    fun k x => Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hTmono : Monotone (fun k => birkhoffSum (σ : Ω → Ω) (fun y => |f 1 y|) k ω) :=
    birkhoffSum_mono_of_nonneg (fun x => abs_nonneg _) ω
  have hSnn : (0 : ℝ) ≤ birkhoffSum (σ : Ω → Ω) (gapMaj σ jω A f) n ω :=
    Finset.sum_nonneg (fun _ _ => gapMaj_nonneg σ jω A f _)
  have hHnn : (0 : ℝ) ≤ birkhoffSum (σ : Ω → Ω) (gapCount σ jω A) n ω :=
    Finset.sum_nonneg (fun _ _ => gapCount_nonneg σ jω A _)
  have hqnn : (0 : ℝ) ≤ |q| := abs_nonneg q
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hnnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hbn : lastBlock σ jω A n ω ≤ n := bWalk_blockCount_le _ _ _ _ _
  have hfg : firstGap σ jω A n ω ≤ n := min_le_right _ _
  by_cases hbad : ω ∈ badSet σ jω A M n
  · rw [Set.indicator_of_mem hbad, Set.indicator_of_mem hbad]
    have h1 : birkhoffSum (σ : Ω → Ω) (fun y => |f 1 y|) (firstGap σ jω A n ω) ω
        ≤ birkhoffSum (σ : Ω → Ω) (fun y => |f 1 y|) n ω := hTmono hfg
    have h2 := hTnn (lastBlock σ jω A n ω) ω
    have h3 : ((n - lastBlock σ jω A n ω : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.sub_le n (lastBlock σ jω A n ω)
    have h4 : ((firstGap σ jω A n ω : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hfg
    have h5 := hTnn M ω
    have h6 := hTnn M ((σ : Ω → Ω)^[n - M] ω)
    have h7 : |q| * (((n - lastBlock σ jω A n ω : ℕ) : ℝ) + ((firstGap σ jω A n ω : ℕ) : ℝ)
          + birkhoffSum (σ : Ω → Ω) (gapCount σ jω A) n ω)
        ≤ |q| * (2 * (M : ℝ) + 2 * (n : ℝ) * 1
          + birkhoffSum (σ : Ω → Ω) (gapCount σ jω A) n ω) :=
      mul_le_mul_of_nonneg_left (by linarith) hqnn
    linarith
  · rw [Set.indicator_of_notMem hbad, Set.indicator_of_notMem hbad]
    have hb1 : firstGap σ jω A n ω < M := by
      by_contra hc
      exact hbad (Or.inl (by rw [not_lt] at hc; exact hc))
    have hb2 : ¬ (lastBlock σ jω A n ω + M ≤ n) := fun hc => hbad (Or.inr hc)
    have h1 : birkhoffSum (σ : Ω → Ω) (fun y => |f 1 y|) (firstGap σ jω A n ω) ω
        ≤ birkhoffSum (σ : Ω → Ω) (fun y => |f 1 y|) M ω := hTmono (le_of_lt hb1)
    have h2 : birkhoffSum (σ : Ω → Ω) (fun y => |f 1 y|) n ω
          - birkhoffSum (σ : Ω → Ω) (fun y => |f 1 y|) (lastBlock σ jω A n ω) ω
        ≤ birkhoffSum (σ : Ω → Ω) (fun y => |f 1 y|) M ((σ : Ω → Ω)^[n - M] ω) := by
      have hmono : birkhoffSum (σ : Ω → Ω) (fun y => |f 1 y|) (n - M) ω
          ≤ birkhoffSum (σ : Ω → Ω) (fun y => |f 1 y|) (lastBlock σ jω A n ω) ω :=
        hTmono (by omega)
      have hshift := birkhoffSum_shift_eq (σ := (σ : Ω → Ω)) (fun y => |f 1 y|) (n - M) M ω
      rw [show n - M + M = n from by omega] at hshift
      linarith
    have h3 : ((n - lastBlock σ jω A n ω : ℕ) : ℝ) ≤ (M : ℝ) := by
      have h : n - lastBlock σ jω A n ω ≤ M := by omega
      exact_mod_cast h
    have h4 : ((firstGap σ jω A n ω : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_of_lt hb1
    have h7 : |q| * (((n - lastBlock σ jω A n ω : ℕ) : ℝ) + ((firstGap σ jω A n ω : ℕ) : ℝ)
          + birkhoffSum (σ : Ω → Ω) (gapCount σ jω A) n ω)
        ≤ |q| * (2 * (M : ℝ) + 2 * (n : ℝ) * 0
          + birkhoffSum (σ : Ω → Ω) (gapCount σ jω A) n ω) :=
      mul_le_mul_of_nonneg_left (by linarith) hqnn
    have h5 := hTnn M ω
    linarith

/-- Birkhoff sums of an integrable function are integrable. -/
theorem integrable_birkhoffSum {μ : Measure Ω} {σ : Ω → Ω} (hmp : MeasurePreserving σ μ μ)
    {g : Ω → ℝ} (hg : Integrable g μ) (n : ℕ) :
    Integrable (fun ω => birkhoffSum σ g n ω) μ := by
  simp only [birkhoffSum]
  exact integrable_finsetSum _ (fun i _ => (hmp.iterate i).integrable_comp_of_integrable hg)

/-- Composing with an iterate of a measure-preserving map does not change the integral. -/
theorem integral_comp_iterate {μ : Measure Ω} {σ : Ω → Ω} (hmp : MeasurePreserving σ μ μ)
    {g : Ω → ℝ} (hg : Integrable g μ) (k : ℕ) :
    ∫ ω, g (σ^[k] ω) ∂μ = ∫ ω, g ω ∂μ := by
  have hmap : Measure.map (σ^[k]) μ = μ := (hmp.iterate k).map_eq
  calc ∫ ω, g (σ^[k] ω) ∂μ = ∫ ω, g ω ∂(Measure.map (σ^[k]) μ) :=
        (integral_map (hmp.iterate k).measurable.aemeasurable
          (by rw [hmap]; exact hg.aestronglyMeasurable)).symm
    _ = ∫ ω, g ω ∂μ := by rw [hmap]

/-- `∫ gapMaj = ∫_B |f₁| + ∫_{Λ₊} |f₁|`. -/
theorem integral_gapMaj {μ : Measure Ω} {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ} {f : ℕ → Ω → ℝ}
    (hB : MeasurableSet (uncovered σ jω A)) (hP : MeasurableSet (rightEnd σ jω '' A))
    (hg : Integrable (f 1) μ) :
    ∫ ω, gapMaj σ jω A f ω ∂μ
      = (∫ ω in uncovered σ jω A, |f 1 ω| ∂μ) + ∫ ω in rightEnd σ jω '' A, |f 1 ω| ∂μ := by
  have habs : Integrable (fun ω => |f 1 ω|) μ := hg.abs
  have hrfl : ∫ ω, gapMaj σ jω A f ω ∂μ
      = ∫ ω, ((uncovered σ jω A).indicator (fun y => |f 1 y|) ω
          + (rightEnd σ jω '' A).indicator (fun y => |f 1 y|) ω) ∂μ := rfl
  rw [hrfl, integral_add (habs.indicator hB) (habs.indicator hP), integral_indicator hB,
    integral_indicator hP]

/-- `∫ gapCount = μ B + μ Λ₊`. -/
theorem integral_gapCount {μ : Measure Ω} [IsFiniteMeasure μ] {σ : Ω ≃ᵐ Ω} {A : Set Ω}
    {jω : Ω → ℕ} (hB : MeasurableSet (uncovered σ jω A))
    (hP : MeasurableSet (rightEnd σ jω '' A)) :
    ∫ ω, gapCount σ jω A ω ∂μ
      = (μ (uncovered σ jω A)).toReal + (μ (rightEnd σ jω '' A)).toReal := by
  have hrfl : ∫ ω, gapCount σ jω A ω ∂μ
      = ∫ ω, ((uncovered σ jω A).indicator (fun _ => (1 : ℝ)) ω
          + (rightEnd σ jω '' A).indicator (fun _ => (1 : ℝ)) ω) ∂μ := rfl
  rw [hrfl, integral_add ((integrable_const (1 : ℝ)).indicator hB)
    ((integrable_const (1 : ℝ)).indicator hP), integral_indicator hB, integral_indicator hP]
  simp [measureReal_def]

end MultiplicativeErgodic
