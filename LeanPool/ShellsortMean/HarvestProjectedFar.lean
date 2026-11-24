/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, diagnostics, and proof consolidation. -/

module

public import LeanPool.ShellsortMean.Actual214LowGrid
public import LeanPool.ShellsortMean.RoughGapFarInteraction
public import LeanPool.ShellsortMean.HarvestActualRings
public import LeanPool.ShellsortMean.RoughGapDenominatorAverage
public import LeanPool.ShellsortMean.FiniteFourier

/-! The high-denominator inverse Fourier kernel on a genuine interval.
All transforms are unnormalized. -/
@[expose] public noncomputable section
namespace Shellsort.HarvestProjectedFar
open Finset ZMod
open scoped ComplexConjugate

variable {h : ℕ} [NeZero h]

/-- Fourier coefficient of weighted physical positions (negative sign). -/
def coeff {ι : Type*} [Fintype ι] (loc : ι → ℕ) (v : ι → ℂ) (k : ZMod h) : ℂ :=
  ∑ i, stdAddChar (-((loc i : ZMod h) * k)) * v i

private theorem abs_char (j : ZMod h) : ‖stdAddChar j‖ = 1 := by
  rw [stdAddChar_apply, Circle.norm_coe]

theorem coeff_norm {ι : Type*} [Fintype ι] (loc : ι → ℕ) (v : ι → ℂ) (k : ZMod h) :
    ‖coeff loc v k‖ ≤ ∑ i, ‖v i‖ := by
  simpa only [coeff, norm_mul, abs_char, one_mul] using
    (norm_sum_le (univ : Finset ι) (fun i => stdAddChar (-((loc i : ZMod h) * k)) * v i))

private theorem range_sum (f : ZMod h → ℂ) :
    (∑ a ∈ range h, f (a : ZMod h)) = ∑ k, f k := by
  rw [← Fin.sum_univ_eq_sum_range]
  let e : Fin h ≃ ZMod h :=
    { toFun := fun a => (a.val : ZMod h)
      invFun := fun k => ⟨k.val, k.val_lt⟩
      left_inv := fun a => Fin.ext (val_natCast_of_lt a.isLt)
      right_inv := natCast_zmod_val }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

private theorem orthog (d : ZMod h) :
    (∑ k, stdAddChar (d * k)) = if d = 0 then (h : ℂ) else 0 := by
  split_ifs with hd
  · simp [hd, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (isPrimitive_stdAddChar h hd)

/-- Summing all phases recovers precisely the residue bucket at the query slot. -/
theorem full_kernel {ι : Type*} [Fintype ι] (loc : ι → ℕ) (v : ι → ℂ) (b : ℕ) :
    (∑ a ∈ range h, coeff loc v (a : ZMod h) * stdAddChar ((b : ZMod h) * (a : ZMod h))) =
      (h : ℂ) * ∑ i, if (loc i : ZMod h) = (b : ZMod h) then v i else 0 := by
  rw [range_sum (fun k => coeff loc v k * stdAddChar ((b : ZMod h) * k))]
  simp only [coeff, sum_mul]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro i _
  have factor (k : ZMod h) :
      stdAddChar (-((loc i : ZMod h) * k)) * v i * stdAddChar ((b : ZMod h) * k) =
        stdAddChar (((b : ZMod h) - (loc i : ZMod h)) * k) * v i := by
    rw [sub_mul, sub_eq_neg_add, AddChar.map_add_eq_mul]; ring
  simp only [factor, ← sum_mul, orthog]
  by_cases eq : (loc i : ZMod h) = (b : ZMod h)
  · simp [eq]
  · simp [eq, sub_ne_zero.mpr (Ne.symm eq)]

private theorem full_interval {len : ℕ} (start b : ℕ) (v : Fin len → ℂ)
    (unit : ∀ i, ‖v i‖ ≤ 1) :
    ‖∑ a ∈ range h, coeff (fun i : Fin len => start + i.val) v (a : ZMod h) *
      stdAddChar ((b : ZMod h) * (a : ZMod h))‖ ≤ h + (len : ℝ) := by
  have hh := NeZero.pos h
  let F := (univ : Finset (Fin len)).filter
    (fun i => ((start + i.val : ℕ) : ZMod h) = (b : ZMod h))
  have bound : F.card ≤ len / h + 1 := by
    convert RoughGapFarInteraction.interval_capacity (length := len) hh start
      ⟨b % h, Nat.mod_lt _ hh⟩ using 1
    congr 1
    ext i
    simp only [F, mem_filter, mem_univ, true_and, natCast_eq_natCast_iff',
      RoughGapFarInteraction.intervalResidue, Fin.ext_iff]
  have vbound : ‖∑ i ∈ F, v i‖ ≤ (F.card : ℝ) :=
    (norm_sum_le F v).trans (by simpa using sum_le_sum (s := F) (fun i _ => unit i))
  rw [full_kernel, norm_mul, Complex.norm_natCast, ← sum_filter]
  have hpos : 0 ≤ (h : ℝ) := by positivity
  have cb : (F.card : ℝ) ≤ (len / h : ℕ) + 1 := by exact_mod_cast bound
  have hb : ((len / h : ℕ) : ℝ) * (h : ℝ) ≤ len := by exact_mod_cast Nat.div_mul_le_self len h
  exact (mul_le_mul_of_nonneg_left (vbound.trans cb) hpos).trans (by nlinarith)

/-- Zero and low-denominator deletions cost at most one interval mass per deleted mode. -/
theorem high_interval_kernel {len : ℕ} (D start b : ℕ) (v : Fin len → ℂ)
    (unit : ∀ i, ‖v i‖ ≤ 1) :
    ‖∑ a ∈ (range h).filter (fun a => 0 < a ∧ D < h / Nat.gcd h a),
      coeff (fun i : Fin len => start + i.val) v (a : ZMod h) *
        stdAddChar ((b : ZMod h) * (a : ZMod h))‖ ≤ h + (2 + (D : ℝ) ^ 2) * len := by
  let G := (range h).filter (fun a => 0 < a ∧ D < h / Nat.gcd h a)
  let E := range h \ G
  let f (a : ℕ) := coeff (fun i : Fin len => start + i.val) v (a : ZMod h) *
    stdAddChar ((b : ZMod h) * (a : ZMod h))
  have sub : E ⊆ insert 0 (Actual214.lowGrid h D) := by
    intro a ha
    obtain ⟨ha, hb⟩ := mem_sdiff.mp ha
    by_cases hz : a = 0
    · simp [hz]
    · apply mem_insert_of_mem
      apply mem_filter.mpr
      exact ⟨ha, Nat.pos_of_ne_zero hz, le_of_not_gt (fun hd =>
        hb (mem_filter.mpr ⟨ha, Nat.pos_of_ne_zero hz, hd⟩))⟩
  have card : E.card ≤ D ^ 2 + 1 := (card_le_card sub).trans
    ((card_insert_le ..).trans (Nat.add_le_add_right (Actual214.lowGrid_card_le h D) 1))
  have each (a : ℕ) : ‖f a‖ ≤ (len : ℝ) := by
    unfold f
    rw [norm_mul, abs_char, mul_one]
    apply (coeff_norm ..).trans
    simpa using sum_le_sum (s := univ) (fun i _ => unit i)
  have small : ‖∑ a ∈ E, f a‖ ≤ (D ^ 2 + 1 : ℕ) * (len : ℝ) := by
    apply (norm_sum_le E f).trans
    apply (sum_le_sum (s := E) (fun a _ => each a)).trans
    simp only [sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast card
  have add := sum_sdiff (s₁ := G) (s₂ := range h) (f := f) (filter_subset ..)
  have diff : (∑ a ∈ G, f a) = (∑ a ∈ range h, f a) - ∑ a ∈ E, f a := by
    change (∑ a ∈ E, f a) + (∑ a ∈ G, f a) = _ at add
    rw [← add]; ring
  change ‖∑ a ∈ G, f a‖ ≤ _
  rw [diff]
  apply (norm_sub_le ..).trans
  apply (add_le_add (full_interval (h := h) start b v unit) small).trans
  push_cast; ring_nf; exact le_rfl

/-- Each outer weight evaluates the bounded projected kernel at its own slot.
The two vectors may overlap and have arbitrary signs. -/
theorem high_far_cross {len : ℕ} {κ : Type*} [Fintype κ] (D start : ℕ) (v : Fin len → ℂ)
    (unit : ∀ i, ‖v i‖ ≤ 1) (loc : κ → ℕ) (w : κ → ℂ) :
    ‖∑ a ∈ (range h).filter (fun a => 0 < a ∧ D < h / Nat.gcd h a),
      coeff (fun i : Fin len => start + i.val) v (a : ZMod h) *
        conj (coeff loc w (a : ZMod h))‖ ≤
      (h + (2 + (D : ℝ) ^ 2) * len) * ∑ i, ‖w i‖ := by
  let G := (range h).filter (fun a => 0 < a ∧ D < h / Nat.gcd h a)
  let X (a : ℕ) := coeff (fun i : Fin len => start + i.val) v (a : ZMod h)
  let K (j : κ) := ∑ a ∈ G, X a * stdAddChar ((loc j : ZMod h) * (a : ZMod h))
  have cross (a : ℕ) : X a * conj (coeff loc w (a : ZMod h)) =
      ∑ j, (X a * stdAddChar ((loc j : ZMod h) * (a : ZMod h))) * conj (w j) := by
    simp only [coeff, map_sum, map_mul, FiniteFourier.stdAddChar_conj_neg, mul_sum, mul_assoc]
  change ‖∑ a ∈ G, X a * conj (coeff loc w (a : ZMod h))‖ ≤ _
  simp_rw [cross]
  rw [sum_comm]
  simp_rw [← sum_mul]
  change ‖∑ j, K j * conj (w j)‖ ≤ _
  apply (norm_sum_le ..).trans
  rw [mul_sum]
  apply sum_le_sum
  intro j _
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_right (high_interval_kernel D start (loc j) v unit) (norm_nonneg _)

/-- Equality with the physical exponential (including its sign and normalization). -/
theorem coeff_exp {ι : Type*} [Fintype ι] (loc : ι → ℕ) (v : ι → ℂ) (a : ℕ) :
    coeff loc v (a : ZMod h) =
      ∑ i, Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (loc i) * a / h) * v i := by
  unfold coeff
  apply sum_congr rfl
  intro i _
  congr 1
  rw [show - ((loc i : ZMod h) * (a : ZMod h)) = ((-((loc i : ℤ) * a) : ℤ) : ZMod h) by
    push_cast; rfl,
    stdAddChar_coe]
  congr 1
  push_cast
  ring

theorem coeff_energy {len : ℕ} (v : Fin len → ℂ) (a : ℕ) :
    ‖coeff (fun i : Fin len => i.val) v (a : ZMod h)‖ ^ 2 =
      RoughGapDenominatorAverage.energy 0 v (a, h) := by
  simp [coeff_exp, RoughGapDenominatorAverage.energy]

open HarvestActualRings in
theorem coeff_pad {n L : ℕ} (a : ℕ) (u : Fin n → ℝ)
    (support : ∀ i, u i ≠ 0 → a ≤ i.val ∧ i.val < a + L) (k : ZMod h) :
    coeff (fun i : Fin n => i.val) (fun i => (u i : ℂ)) k =
      coeff (fun i : Fin L => a + i.val) (fun i => (pad (α := ℝ) a u i : ℂ)) k := by
  unfold coeff
  let weighted (i : Fin n) := stdAddChar (-((i.val : ZMod h) * k)) * (u i : ℂ)
  have hs (i : Fin n) (nz : weighted i ≠ 0) := support i (fun z => nz (by simp [weighted, z]))
  change (∑ i, weighted i) = _
  rw [pad_sum a weighted hs]
  apply sum_congr rfl
  intro j _
  by_cases hj : a + j.val < n <;> simp [pad, hj, weighted]

open HarvestActualRings RoughGapEndpoint in
/-- Actual threshold error: merge all rings through j, then test against ring k
at precisely the surviving frequencies on the chosen gap grid. -/
theorem actual_projected_far {n T H : ℕ} (ht : T ≤ n) (hp : 0 < H)
    (p : RankPlacement n) (D j : ℕ) (k : Fin (n + 1)) :
    ‖∑ a ∈ (range h).filter (fun a => 0 < a ∧ D < h / Nat.gcd h a),
      coeff (fun i : Fin n => i.val) (fun i => (mergedVec ht hp p j i : ℂ)) (a : ZMod h) *
      conj (coeff (fun i : Fin n => i.val) (fun i => (ringVec ht hp p k i : ℂ)) (a : ZMod h))‖ ≤
      (h + (2 + (D : ℝ) ^ 2) * (2 * rad H j : ℕ)) * ∑ i, |(ringVec ht hp p k i : ℝ)| := by
  let u (i : Fin n) := (mergedVec ht hp p j i : ℝ)
  let a := start T (rad H j)
  let L := 2 * rad H j
  have hs (i : Fin n) (nz : u i ≠ 0) : a ≤ i.val ∧ i.val < a + L :=
    merged_nonzero_support ht hp p j i (by dsimp [u] at nz; exact_mod_cast nz)
  have hu (i : Fin L) : ‖(pad (α := ℝ) a u i : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    unfold pad
    split
    · rename_i hi
      dsimp [u]; exact_mod_cast merged_unit ht hp p j ⟨a + i.val, hi⟩
    · norm_num
  have convertInner (t : ZMod h) : coeff (fun i : Fin n => i.val)
        (fun i => (mergedVec ht hp p j i : ℂ)) t =
      coeff (fun i : Fin L => a + i.val) (fun i => (pad (α := ℝ) a u i : ℂ)) t := by
    simpa [u] using coeff_pad (L := L) a u hs t
  simp_rw [convertInner]
  simpa [L, Complex.norm_intCast] using high_far_cross (h := h) D a _ hu
    (fun i : Fin n => i.val) (fun i => (ringVec ht hp p k i : ℂ))





end Shellsort.HarvestProjectedFar
