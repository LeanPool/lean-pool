/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorGauge
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedNonPluripolar

/-!
# Gauge invariance of the mixed non-pluripolar truncation limit

Adding smooth functions with vanishing complex Hessian to plurisubharmonic
slots does not change the mixed truncation-limit measure. On the common strict
loci of `v + h` at level `k` and of `v` at level `m`, the bounded products of the
two truncations agree with the product of `max(max(v, -m) + h, -k)`: once by
max-constant locality, once by locality for the pluriharmonic obstacle `-m + h`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.MixedNonPluripolar

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open FirstPass.MixedNonPluripolar MixedMongeAmpere BedfordTaylor

variable {n : ℕ}

theorem ereal_coe_max (a b : ℝ) : max (a : EReal) (b : EReal) = ((max a b : ℝ) : EReal) :=
  (Monotone.map_max EReal.coe_strictMono.monotone).symm

theorem truncationReal_coe_add_max {x : EReal} (hx : x ≠ ⊤) (t : ℝ) (k m : ℕ) :
    max ((max x ((-(m : ℝ) : ℝ) : EReal)).toReal + t) (-(k : ℝ)) =
      max ((max (x + (t : EReal)) ((-(k : ℝ) : ℝ) : EReal)).toReal) (-(m : ℝ) + t) := by
  induction x using EReal.rec with
  | bot =>
    rw [max_eq_right bot_le, EReal.bot_add, max_eq_right bot_le, EReal.toReal_coe,
      EReal.toReal_coe, max_comm]
  | top => exact absurd rfl hx
  | coe r =>
    rw [ereal_coe_max, EReal.toReal_coe, ← EReal.coe_add, ereal_coe_max, EReal.toReal_coe,
      ← max_add_add_right, max_right_comm]

theorem isSmoothPluriharmonicOn_const_add {Ω : Opens (ComplexModel n)} {h : ComplexModel n → ℝ}
    (hh : IsSmoothPluriharmonicOn Ω h) (c : ℝ) :
    IsSmoothPluriharmonicOn Ω fun z ↦ c + h z := by
  refine ⟨contDiffOn_const.add hh.1, fun z hz ↦ ?_⟩
  rw [complexHessian_add_of_isSmoothPluriharmonicOn (f := fun _ ↦ c) contDiffOn_const hh hz]
  ext j k; simp [complexHessian]

/-- **Gauge invariance of the mixed truncation limit.** -/
theorem mixedTruncationLimitMeasure_add_pluriharmonic {Ω : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → EReal} (hv : ∀ i, PlurisubharmonicOn (v i) Ω)
    {h : Fin n → ComplexModel n → ℝ} (hh : ∀ i, IsSmoothPluriharmonicOn Ω (h i))
    (hvh : ∀ i, PlurisubharmonicOn (fun z ↦ v i z + (h i z : EReal)) Ω) :
    mixedTruncationLimitMeasure Ω (fun i z ↦ v i z + (h i z : EReal)) hvh =
      mixedTruncationLimitMeasure Ω v hv := by
  classical
  set w : Fin n → ComplexModel n → EReal := fun i z ↦ v i z + (h i z : EReal) with hw_def
  symm
  refine mixedTruncationLimitMeasure_unique hvh (mixedTruncationLimitMeasure_compl hv) ?_ ?_
  · have hpole : componentPoleSet w = componentPoleSet v := by
      ext z
      simp [componentPoleSet, hw_def, EReal.add_eq_bot_iff]
    rw [hpole]
    exact mixedTruncationLimitMeasure_poleSet hv
  intro k
  set L := commonStrictLocus Ω w k with hL_def
  have hLv (z : ComplexModel n) (hz : z ∈ L) (i : Fin n) : v i z ≠ ⊥ := fun hbot ↦ by
    have := hz.2 i
    simp [hw_def, hbot] at this
  have hLcover : L = ⋃ m : ℕ, L ∩ commonStrictLocus Ω v m := by
    refine subset_antisymm (fun z hz ↦ ?_) (iUnion_subset fun m ↦ inter_subset_left)
    have hzv : z ∈ ⋃ m, commonStrictLocus Ω v m := by
      rw [iUnion_commonStrictLocus]
      exact ⟨hz.1, fun i ↦ hLv z hz i⟩
    obtain ⟨m, hm⟩ := mem_iUnion.1 hzv
    exact mem_iUnion.2 ⟨m, hz, hm⟩
  change (mixedTruncationLimitMeasure Ω v hv).restrict L =
    (canonicalMixedBedfordTaylorMeasure Ω (mixedTruncationReal w k)
      (mixedTruncationReal_isLocallyBounded hvh k)).restrict L
  rw [hLcover]
  refine Measure.restrict_iUnion_congr.2 fun m ↦ ?_
  set S := L ∩ commonStrictLocus Ω v m with hS_def
  set a := mixedTruncationReal v m with ha_def
  set b := mixedTruncationReal w k with hb_def
  set μa := canonicalMixedBedfordTaylorMeasure Ω a (mixedTruncationReal_isLocallyBounded hv m)
  set μb := canonicalMixedBedfordTaylorMeasure Ω b (mixedTruncationReal_isLocallyBounded hvh k)
  have hlim : (mixedTruncationLimitMeasure Ω v hv).restrict S = μa.restrict S := by
    rw [← Measure.restrict_restrict_of_subset (inter_subset_right : S ⊆ _),
      mixedTruncationLimitMeasure_restrict_commonStrictLocus hv m, mixedTruncationMeasure,
      Measure.restrict_restrict_of_subset (inter_subset_right : S ⊆ _)]
  rw [hlim]
  have ha : IsBTLimit Ω a μa :=
    IsLocalMixedBedfordTaylorMeasure.isBTLimit (canonicalMixedBedfordTaylorMeasure_spec _ _ _)
  have hb : IsBTLimit Ω b μb :=
    IsLocalMixedBedfordTaylorMeasure.isBTLimit (canonicalMixedBedfordTaylorMeasure_spec _ _ _)
  obtain ⟨τ, hτ⟩ := ha.exists_add_pluriharmonic hh (-(k : ℝ))
  -- values on the strict loci
  have hreal (z : ComplexModel n) (hz : z ∈ S) (i : Fin n) :
      ∃ r : ℝ, v i z = r ∧ -(m : ℝ) < r ∧ -(k : ℝ) < r + h i z := by
    have hzΩ := hz.1.1
    obtain ⟨r, hr⟩ : ∃ r : ℝ, v i z = r :=
      ⟨(v i z).toReal, (EReal.coe_toReal ((hv i z hzΩ).ne_top) (hLv z hz.1 i)).symm⟩
    refine ⟨r, hr, ?_, ?_⟩
    · have := hz.2.2 i
      rw [hr] at this
      exact EReal.coe_lt_coe_iff.mp this
    · have := hz.1.2 i
      simp only [hw_def, hr, ← EReal.coe_add] at this
      exact EReal.coe_lt_coe_iff.mp this
  have ha_ge (z : ComplexModel n) (i : Fin n) (r : ℝ) (hr : v i z = r) : r ≤ a i z := by
    change r ≤ (max (v i z) ((-(m : ℝ) : ℝ) : EReal)).toReal
    rw [hr, ereal_coe_max, EReal.toReal_coe]
    exact le_max_left _ _
  have hb_ge (z : ComplexModel n) (i : Fin n) (r : ℝ) (hr : v i z = r) : r + h i z ≤ b i z := by
    change _ ≤ (max (v i z + (h i z : EReal)) ((-(k : ℝ) : ℝ) : EReal)).toReal
    rw [hr, ← EReal.coe_add, ereal_coe_max, EReal.toReal_coe]
    exact le_max_left _ _
  -- max-constant locality for the base `a + h`
  have hah := ha.add_pluriharmonic hh
  have h2 := restrict_eq_of_max_const (v := fun i z ↦ a i z + h i z)
    (w := fun i z ↦ max (a i z + h i z) (-(k : ℝ))) (-(k : ℝ)) hah.2.1 hτ.2.1 hah.2.2 hτ.2.2
    fun i z _ ↦ rfl
  have hS2 : S ⊆ {z | z ∈ Ω ∧ ∀ i, -(k : ℝ) < a i z + h i z} := fun z hz ↦
    ⟨hz.1.1, fun i ↦ by
      obtain ⟨r, hr, -, hk⟩ := hreal z hz i
      linarith [ha_ge z i r hr]⟩
  -- locality for the pluriharmonic obstacle `-m + h` over the base `b`
  have hφ : ∀ i, IsSmoothPluriharmonicOn Ω (fun z ↦ -(m : ℝ) + h i z) := fun i ↦
    isSmoothPluriharmonicOn_const_add (hh i) _
  have hτ' : IsBTLimit Ω (fun i z ↦ max (b i z) (-(m : ℝ) + h i z)) τ := hτ.congr fun i z hz ↦ by
    change max ((max (v i z) ((-(m : ℝ) : ℝ) : EReal)).toReal + h i z) (-(k : ℝ)) =
      max ((max (v i z + (h i z : EReal)) ((-(k : ℝ) : ℝ) : EReal)).toReal) (-(m : ℝ) + h i z)
    exact truncationReal_coe_add_max ((hv i z hz).ne_top) (h i z) k m
  have h1 := hb.restrict_max_pluriharmonic hτ' hφ fun i z _ ↦ rfl
  have hS1 : S ⊆ {z | z ∈ Ω ∧ ∀ i, -(m : ℝ) + h i z < b i z} := fun z hz ↦
    ⟨hz.1.1, fun i ↦ by
      obtain ⟨r, hr, hm, -⟩ := hreal z hz i
      linarith [hb_ge z i r hr]⟩
  rw [← Measure.restrict_restrict_of_subset hS2, ← h2, Measure.restrict_restrict_of_subset hS2,
    ← Measure.restrict_restrict_of_subset hS1, h1, Measure.restrict_restrict_of_subset hS1]

end SGPT.Foundations.Analysis.Pending.MixedNonPluripolar
