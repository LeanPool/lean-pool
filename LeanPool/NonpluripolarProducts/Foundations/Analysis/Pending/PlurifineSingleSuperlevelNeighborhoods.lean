/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PlurifineSuperlevelNeighborhoods
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshAddition
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PshConvexCone

/-!
# Single-superlevel neighborhoods in the plurifine topology

Combines real plurisubharmonic superlevels into local neighborhoods.
-/

@[expose] public section

open Set TopologicalSpace
open scoped Topology BigOperators

namespace SGPT.Foundations.Analysis.Pending.PlurifineSingleSuperlevelNeighborhoods

open FirstPass FirstPass.MongeAmpere PlurifinePshTopology

noncomputable section

variable {n : ℕ} {Ω : Opens (ComplexModel n)}

private theorem real_psh_add {f g : ComplexModel n → ℝ}
    (hf : PlurisubharmonicOn (fun z => (f z : EReal)) Ω)
    (hg : PlurisubharmonicOn (fun z => (g z : EReal)) Ω) :
    PlurisubharmonicOn (fun z => ((f z + g z : ℝ) : EReal)) Ω := by
  simpa only [EReal.coe_add] using hf.add hg

private theorem real_psh_sum {ι : Type*} (F : Finset ι) (f : ι → ComplexModel n → ℝ)
    (hf : ∀ i ∈ F, PlurisubharmonicOn (fun z => (f i z : EReal)) Ω) :
    PlurisubharmonicOn (fun z => ((∑ i ∈ F, f i z : ℝ) : EReal)) Ω := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using plurisubharmonicOn_const 0 (Ω : Set (ComplexModel n))
  | @insert i F hi ih =>
    simpa only [Finset.sum_insert hi] using
      real_psh_add (hf i (Finset.mem_insert_self i F))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem ordinary_open_sublevel {f : ComplexModel n → ℝ}
    (hf : PlurisubharmonicOn (fun z => (f z : EReal)) Ω) (b : ℝ) :
    IsOpen {z : Ω | f z.val < b} := by
  have hsc : UpperSemicontinuousOn (fun z : Ω => (f z.val : EReal)) univ :=
    hf.upperSemicontinuousOn.comp continuous_subtype_val.continuousOn
      (fun z _ => z.property)
  convert (upperSemicontinuousOn_univ_iff.mp hsc).isOpen_preimage (b : EReal) using 1
  ext z
  simp only [mem_ofPred_eq, mem_preimage, mem_Iio, EReal.coe_lt_coe_iff]

/-- A bounded genuine PSH strict superlevel neighborhood is produced from the
actual fine-open set, without a supplied local generator or a covering certificate. -/
theorem exists_bounded_single_superlevel {S : Set Ω}
    (hS : IsOpen[topology Ω] S) {x : Ω} (hx : x ∈ S) :
    ∃ (O : Set Ω) (g : ComplexModel n → ℝ),
      IsOpen O ∧ x ∈ O ∧ PlurisubharmonicOn (fun z => (g z : EReal)) Ω ∧
      g x.val = 1 / 2 ∧ (∀ z ∈ Ω, -1 ≤ g z) ∧ (∀ z ∈ O, g z.val ≤ 1) ∧
      IsOpen[topology Ω] (O ∩ {z : Ω | 0 < g z.val}) ∧
      O ∩ {z : Ω | 0 < g z.val} ⊆ S := by
  classical
  obtain ⟨F, a, O₀, ho₀, hx₀, ha, hbopen, hbsub⟩ :=
    PlurifineSuperlevelNeighborhoods.exists_ordinary_open_finite_superlevels hS hx
  let m : ℝ := F.card
  let δ : ℝ := 1 / (2 * (m + 1))
  have hm : 0 ≤ m := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : 2 * (m + 1) * δ = 1 := by
    dsimp only [δ]
    field_simp
  have hmδ : m * δ ≤ 1 / 2 := by nlinarith
  let f : realPshFunctions Ω → ComplexModel n → ℝ :=
    fun t z => (t.val z - a t) / (t.val x.val - a t)
  have hfx (t) (ht : t ∈ F) : f t x.val = 1 := by
    dsimp only [f]
    exact div_self (sub_pos.mpr (ha t ht)).ne'
  have hf (t) (ht : t ∈ F) :
      PlurisubharmonicOn (fun z => (f t z : EReal)) Ω := by
    have h := (t.property.add_const (-a t)).const_mul
      (inv_pos.mpr (sub_pos.mpr (ha t ht)))
    simpa only [f, div_eq_mul_inv, sub_eq_add_neg, EReal.coe_mul,
      EReal.coe_add, EReal.coe_neg, mul_comm] using h
  let P : Set Ω := {z : Ω | ∀ t ∈ F, f t z.val < 1 + δ}
  have hp : IsOpen P := by
    convert isOpen_biInter_finset (fun t ht => ordinary_open_sublevel (hf t ht) (1 + δ))
      using 1
    ext z
    simp only [P, mem_ofPred_eq, mem_iInter]
  have hpf : IsOpen[topology Ω] P := by
    let : TopologicalSpace Ω := topology Ω
    convert isOpen_biInter_finset (fun t ht => isOpen_realPsh_sublevel (hf t ht) (1 + δ))
      using 1
    ext z
    simp only [P, mem_ofPred_eq, mem_iInter]
  let O := O₀ ∩ P
  let h : ComplexModel n → ℝ := fun z => (∑ t ∈ F, f t z) - (m - 1 / 2)
  have hh : PlurisubharmonicOn (fun z => (h z : EReal)) Ω := by
    simpa only [h, sub_eq_add_neg, EReal.coe_add, EReal.coe_neg] using
      (real_psh_sum F f hf).add_const (-(m - 1 / 2))
  let g : ComplexModel n → ℝ := fun z => max (h z) (-1)
  have hg : PlurisubharmonicOn (fun z => (g z : EReal)) Ω := by
    convert hh.max (plurisubharmonicOn_const (-1) (Ω : Set (ComplexModel n))) using 1
    funext z
    rcases le_total (h z) (-1 : ℝ) with hz | hz
    · simp only [g, max_eq_right hz, max_eq_right (EReal.coe_le_coe_iff.mpr hz)]
    · simp only [g, max_eq_left hz, max_eq_left (EReal.coe_le_coe_iff.mpr hz)]
  have hgx : g x.val = 1 / 2 := by
    have hxsum : (∑ t ∈ F, f t x.val) = m := by
      calc
        _ = ∑ _t ∈ F, (1 : ℝ) := Finset.sum_congr rfl hfx
        _ = m := by simp [m]
    simp only [g, h, hxsum]
    rw [show m - (m - 1 / 2) = (1 / 2 : ℝ) by ring]
    norm_num
  have hgle (z : Ω) (hz : z ∈ O) : g z.val ≤ 1 := by
    have hs : (∑ t ∈ F, f t z.val) ≤ m * (1 + δ) := by
      calc
        _ ≤ ∑ _t ∈ F, (1 + δ) :=
          Finset.sum_le_sum (fun t ht => (hz.2 t ht).le)
        _ = m * (1 + δ) := by simp only [Finset.sum_const, nsmul_eq_mul]; rfl
    dsimp only [g, h]
    apply max_le
    · nlinarith
    · norm_num
  have hlower (z : Ω) (hz : z ∈ O) (hgz : 0 < g z.val) :
      ∀ t ∈ F, a t < t.val z.val := by
    have hhz : 0 < h z.val := by
      simpa only [g, lt_max_iff, show ¬(0 : ℝ) < -1 by norm_num, or_false] using hgz
    intro t ht
    by_contra hbad
    have hft : f t z.val ≤ 0 := by
      dsimp only [f]
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (not_lt.mp hbad))
        (sub_pos.mpr (ha t ht)).le
    have hcard : (F.erase t).card + 1 = F.card := Finset.card_erase_add_one ht
    have hmc : ((F.erase t).card : ℝ) = m - 1 := by
      have hc : ((F.erase t).card : ℝ) + 1 = m := by
        dsimp only [m]
        exact_mod_cast hcard
      linarith
    have hs : (∑ j ∈ F, f j z.val) ≤ (m - 1) * (1 + δ) := by
      rw [← Finset.sum_erase_add _ _ ht]
      calc
        _ ≤ (∑ _j ∈ F.erase t, (1 + δ)) + 0 :=
          add_le_add (Finset.sum_le_sum (fun j hj =>
            (hz.2 j (Finset.mem_of_mem_erase hj)).le)) hft
        _ = (m - 1) * (1 + δ) := by simp only [Finset.sum_const, nsmul_eq_mul, hmc, add_zero]
    have hm1 : 1 ≤ m := by
      change (1 : ℝ) ≤ (F.card : ℝ)
      exact_mod_cast Finset.one_le_card.mpr ⟨t, ht⟩
    dsimp only [h] at hhz
    nlinarith
  have heq : O ∩ {z : Ω | 0 < g z.val} =
      (O₀ ∩ {z : Ω | ∀ t ∈ F, a t < t.val z.val}) ∩ P ∩
        {z : Ω | 0 < g z.val} := by
    ext z
    constructor
    · intro hz
      exact ⟨⟨⟨hz.1.1, hlower z hz.1 hz.2⟩, hz.1.2⟩, hz.2⟩
    · intro hz
      exact ⟨⟨hz.1.1.1, hz.1.2⟩, hz.2⟩
  refine ⟨O, g, ho₀.inter hp, ⟨hx₀, ?_⟩, hg, hgx,
    (fun z _ => le_max_right _ _), hgle, ?_, ?_⟩
  · intro t ht
    rw [hfx t ht]
    linarith
  · rw [heq]
    let : TopologicalSpace Ω := topology Ω
    exact (hbopen.inter hpf).inter (isOpen_realPsh_superlevel hg 0)
  · intro z hz
    exact hbsub ⟨hz.1.1, hlower z hz.1 hz.2⟩

end

end SGPT.Foundations.Analysis.Pending.PlurifineSingleSuperlevelNeighborhoods
