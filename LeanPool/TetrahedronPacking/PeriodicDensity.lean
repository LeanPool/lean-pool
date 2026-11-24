/-
Copyright (c) 2026 Mike Lady. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Lady
-/

-- Modified for Lean Pool.

module

public import LeanPool.TetrahedronPacking.PackingMeasure
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Density of a periodic convex packing

Count full copies with lattice shifts in the inner and outer concentric
cubes. The lattice counting theorem gives the same normalization for the two
counts, since adding a fixed margin to the radius preserves their limits.
-/

@[expose] public section

namespace TetrahedronPacking

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise Topology

theorem periodic_convex_density
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ι → Set (κ → ℝ)) (d : ℝ)
    (hc : ∀ i, Convex ℝ (s i)) (hb : ∀ i x, x ∈ s i → ‖x‖ ≤ d)
    (hd : Pairwise fun p q : ι × L =>
      Disjoint (interior ((p.2 : κ → ℝ) +ᵥ s p.1))
        (interior ((q.2 : κ → ℝ) +ᵥ s q.1))) :
    Tendsto (fun R : ℝ =>
      volume.real ((⋃ p : ι × L, (p.2 : κ → ℝ) +ᵥ s p.1) ∩ Metric.closedBall 0 R) /
        volume.real (Metric.closedBall (0 : κ → ℝ) R))
      atTop (𝓝 ((∑ i, volume.real (s i)) / ZLattice.covolume L)) := by
  classical
  let n := Fintype.card κ
  let B (R : ℝ) := Metric.closedBall (0 : κ → ℝ) R
  let J (R : ℝ) := {j : L // ‖(j : κ → ℝ)‖ ≤ R}
  let U (R : ℝ) := ⋃ p : ι × J R, ((p.2.val : L) : κ → ℝ) +ᵥ s p.1
  let C := ⋃ p : ι × L, (p.2 : κ → ℝ) +ᵥ s p.1
  let V := ∑ i, volume.real (s i)
  have hB (R : ℝ) : volume (B R) ≠ ∞ := Metric.isBounded_closedBall.measure_lt_top.ne
  have hs (i : ι) : volume (s i) ≠ ∞ := by
    apply ne_top_of_le_ne_top (hB d)
    apply measure_mono
    intro x hx
    simpa [B, Metric.mem_closedBall, dist_zero_right] using hb i x hx
  have hU (R : ℝ) :
      volume.real (U R) = (Nat.card (B R ∩ L : Set (κ → ℝ)) : ℝ) * V ∧
        volume (U R) ≠ ∞ := by
    have hf : (B R ∩ L : Set (κ → ℝ)).Finite := by
      let : DiscreteTopology L.toAddSubgroup := ‹DiscreteTopology L›
      exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
        Metric.isBounded_closedBall L.toAddSubgroup.isClosed_of_discreteTopology
    let e : J R ≃ (B R ∩ L : Set (κ → ℝ)) :=
      { toFun := fun j => ⟨j.val.val, ⟨by simpa [B, Metric.mem_closedBall, dist_zero_right]
          using j.property, j.val.property⟩⟩
        invFun := fun x => ⟨⟨x.val, x.property.2⟩,
          by simpa [B, Metric.mem_closedBall, dist_zero_right] using x.property.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let := hf.fintype
    let : Fintype (J R) := Fintype.ofEquiv _ e.symm
    have hcard : Fintype.card (J R) = Nat.card (B R ∩ L : Set (κ → ℝ)) := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_congr e
    have hm : volume (U R) = ∑ p : ι × J R, volume (s p.1) := by
      have hd' : Pairwise fun p q : ι × J R =>
          Disjoint (interior (((p.2.val : L) : κ → ℝ) +ᵥ s p.1))
            (interior (((q.2.val : L) : κ → ℝ) +ᵥ s q.1)) := by
        intro p q hpq
        apply @hd (p.1, p.2.val) (q.1, q.2.val)
        intro he
        obtain ⟨he₁, he₂⟩ := Prod.mk.inj he
        exact hpq (Prod.ext he₁ (Subtype.ext he₂))
      change volume (⋃ p : ι × J R, ((p.2.val : L) : κ → ℝ) +ᵥ s p.1) = _
      rw [measure_iUnion_of_disjoint_convex_interiors volume
        (fun p : ι × J R => ((p.2.val : L) : κ → ℝ) +ᵥ s p.1)
        (fun p => (hc p.1).vadd _) hd', tsum_fintype]
      simp only [measure_vadd]
    constructor
    · rw [measureReal_def, hm, ENNReal.toReal_sum (fun p _ => hs p.1),
        Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hcard]
      rfl
    · rw [hm]
      exact ENNReal.sum_ne_top.mpr (fun p _ => hs p.1)
  have hbvol (R : ℝ) (hR : 0 ≤ R) :
      volume.real (B R) = (2 : ℝ) ^ n * R ^ n := by
    rw [measureReal_def, Real.volume_pi_closedBall _ hR,
      ENNReal.toReal_ofReal (pow_nonneg (mul_nonneg zero_le_two hR) _), mul_pow]
  have hside (a : ℝ) : Tendsto (fun R => volume.real (U (R + a)) / volume.real (B R))
      atTop (𝓝 (V / ZLattice.covolume L)) := by
    have hv : Tendsto (fun R : ℝ => (R + a) / R) atTop (𝓝 1) := by
      have hz := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul a |>.const_add (1 : ℝ)
      simp only [mul_zero, add_zero] at hz
      refine hz.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      field_simp
    have hcount := (lattice_count_in_coordinate_cubes L).comp
      (tendsto_atTop_add_const_right atTop a tendsto_id)
    have ht := ((hcount.mul (hv.pow n)).mul_const V).div_const ((2 : ℝ) ^ n)
    rw [hbvol 1 zero_le_one] at ht
    simp only [one_pow, mul_one] at ht
    have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have hcov : ZLattice.covolume L ≠ 0 := (ZLattice.covolume_pos L volume).ne'
    have hlim : (2 : ℝ) ^ n / ZLattice.covolume L * V / (2 : ℝ) ^ n =
        V / ZLattice.covolume L := by
      field_simp [hp, hcov]
    rw [hlim] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop (max 0 (-a))] with R hR
    have hR₀ : 0 < R := (le_max_left _ _).trans_lt hR
    have ha : R + a ≠ 0 := ne_of_gt (neg_lt_iff_pos_add.mp ((le_max_right _ _).trans_lt hR))
    change (Nat.card (B (R + a) ∩ L : Set (κ → ℝ)) : ℝ) / (R + a) ^ n *
      ((R + a) / R) ^ n * V / (2 : ℝ) ^ n = volume.real (U (R + a)) / volume.real (B R)
    rw [(hU (R + a)).1, hbvol R hR₀.le, div_pow]
    field_simp [hR₀.ne', ha, hp]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hside (-d)) (hside d) ?_ ?_
  · apply Eventually.of_forall
    intro R
    have h := (covered_window_sandwich s (fun j : L => (j : κ → ℝ)) R d hb).1
    have hfin : volume (C ∩ B R) ≠ ∞ :=
      ne_top_of_le_ne_top (hB R) (measure_mono inter_subset_right)
    apply div_le_div_of_nonneg_right _ measureReal_nonneg
    apply measureReal_mono _ hfin
    rw [← sub_eq_add_neg]
    exact h
  · apply Eventually.of_forall
    intro R
    apply div_le_div_of_nonneg_right _ measureReal_nonneg
    exact measureReal_mono (covered_window_sandwich s (fun j : L => (j : κ → ℝ)) R d hb).2
      (hU (R + d)).2

end TetrahedronPacking
