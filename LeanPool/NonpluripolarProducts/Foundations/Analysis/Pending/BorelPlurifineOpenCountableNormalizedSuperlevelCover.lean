/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ChoquetRegularization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PlurifineSingleSuperlevelNeighborhoods
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PlurifineEuclideanComparison
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PlurifineStrictSuperlevelCover
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RegularizedIncreasingPshGapCapacityZero
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorFixedWeight

/-!
# A countable normalized superlevel cover of a Borel plurifine open set

The genuine original plurifine open set internally produces basic patches.
The Borel remainder has zero literal relative capacity on every ordinary
smaller domain, by testing each original normalized competitor measure.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.BorelPlurifineOpenCountableNormalizedSuperlevelCover

open FirstPass FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

private theorem exists_increasing_sequence {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] {H : Set (X → ℝ)} (hne : H.Nonempty)
    (hmax : ∀ a ∈ H, ∀ b ∈ H, (fun x ↦ max (a x) (b x)) ∈ H) :
    ∃ g : ℕ → X → ℝ, (∀ k, g k ∈ H) ∧
      (∀ x, Monotone (fun k ↦ g k x)) ∧
      uscRegularization (fun x ↦ ⨆ k, (g k x : EReal)) =
        uscRegularization (sSup ((fun h : X → ℝ ↦ fun x ↦ (h x : EReal)) '' H)) := by
  classical
  obtain ⟨s, hs, hseq⟩ := exists_seq_uscRegularization_iSup_eq (hne.image
    (fun h : X → ℝ ↦ fun x ↦ (h x : EReal)))
  have hrep : ∀ k, ∃ a ∈ H, (fun x ↦ (a x : EReal)) = s k := hs
  choose a ha he using hrep
  let g : ℕ → X → ℝ := fun k x ↦ (runningMax s k x).toReal
  have hh : ∀ k, g k ∈ H ∧ (fun x ↦ (g k x : EReal)) = runningMax s k := by
    intro k
    induction k with
    | zero =>
      have h0 : g 0 = a 0 := by
        funext x
        simp only [g, runningMax, ← he 0, EReal.toReal_coe]
      constructor
      · rw [h0]
        exact ha 0
      · rw [h0]
        exact he 0
    | succ k ih =>
      have hm : (fun x ↦ ((max (g k x) (a (k + 1) x) : ℝ) : EReal)) =
          runningMax s (k + 1) := by
        funext x
        change ((max (g k x) (a (k + 1) x) : ℝ) : EReal) =
          max (runningMax s k x) (s (k + 1) x)
        rw [← congrFun ih.2 x, ← congrFun (he (k + 1)) x]
        exact EReal.coe_strictMono.monotone.map_max
      have hstep : g (k + 1) = fun x ↦ max (g k x) (a (k + 1) x) := by
        funext x
        dsimp only [g]
        rw [← congrFun hm x, EReal.toReal_coe]
      constructor
      · rw [hstep]
        exact hmax (g k) ih.1 (a (k + 1)) (ha (k + 1))
      · rw [hstep]
        exact hm
  refine ⟨g, fun k ↦ (hh k).1, ?_, ?_⟩
  · intro x k l hkl
    apply EReal.coe_le_coe_iff.mp
    rw [congrFun (hh k).2 x, congrFun (hh l).2 x]
    exact runningMax_monotone s hkl x
  · have hsup : (fun x ↦ ⨆ k, (g k x : EReal)) = ⨆ k, s k := by
      ext x
      rw [iSup_apply]
      calc
        (⨆ k, (g k x : EReal)) = ⨆ k, runningMax s k x :=
          iSup_congr fun k ↦ congrFun (hh k).2 x
        _ = _ := iSup_runningMax s x
    rw [hsup]
    exact hseq

/-- The original Borel fine-open set internally produces countably many
genuine normalized patches and an all-subdomain capacity-zero remainder. -/
theorem exists_countable_normalized_cover
    {Ω : Opens (ComplexModel n)} {F : Set (ComplexModel n)}
    (hFΩ : F ⊆ (Ω : Set (ComplexModel n))) (hFBorel : MeasurableSet F)
    (hFine : IsOpen[PlurifinePshTopology.topology Ω] (Subtype.val ⁻¹' F)) :
    ∃ (B : ℕ → Opens (ComplexModel n)) (g : ℕ → ℕ → ComplexModel n → ℝ),
      (∀ j, B j ≤ Ω) ∧
      (∀ j k, PlurisubharmonicOn (fun x ↦ (g j k x : EReal)) Ω) ∧
      (∀ j, ∀ x ∈ Ω, Monotone (fun k ↦ g j k x)) ∧
      (∀ j k x, x ∈ B j → -1 ≤ g j k x ∧ g j k x ≤ 1) ∧
      (∀ j k, {x | x ∈ B j ∧ 0 < g j k x} ⊆ F ∧
        MeasurableSet {x | x ∈ B j ∧ 0 < g j k x} ∧
        IsOpen[PlurifinePshTopology.topology Ω]
          (Subtype.val ⁻¹' {x | x ∈ B j ∧ 0 < g j k x})) ∧
      MeasurableSet (F \ ⋃ j, ⋃ k, {x | x ∈ B j ∧ 0 < g j k x}) ∧
      ∀ (D : Opens (ComplexModel n)), D ≤ Ω →
        relCapacity D ((F \ ⋃ j, ⋃ k, {x | x ∈ B j ∧ 0 < g j k x}) ∩
          (D : Set (ComplexModel n))) = 0 := by
  classical
  obtain ⟨b, hbasis⟩ := TopologicalSpace.exists_seq_basis Ω
  let B : ℕ → Opens (ComplexModel n) := fun j ↦
    ⟨Subtype.val '' b j,
      Ω.isOpen.isOpenMap_subtype_val _ (hbasis.isOpen (mem_range_self j))⟩
  have hBΩ (j : ℕ) : B j ≤ Ω := by
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  let H : ℕ → Set (ComplexModel n → ℝ) := fun j ↦
    {h | PlurisubharmonicOn (fun x ↦ (h x : EReal)) Ω ∧
      (∀ x ∈ B j, -1 ≤ h x ∧ h x ≤ 1) ∧
      {x | x ∈ B j ∧ 0 < h x} ⊆ F}
  have hne (j : ℕ) : (H j).Nonempty := by
    refine ⟨fun _ ↦ -1, ?_, ?_, ?_⟩
    · exact fun x _ ↦ plurisubharmonicAt_const ((-1 : ℝ) : EReal)
        (EReal.coe_ne_top (-1)) x
    · intro x hx
      norm_num
    · rintro x ⟨hx, hp⟩
      norm_num at hp
  have hmax (j : ℕ) : ∀ a ∈ H j, ∀ c ∈ H j,
      (fun x ↦ max (a x) (c x)) ∈ H j := by
    rintro a ⟨hpa, hba, hFa⟩ c ⟨hpc, hbc, hFc⟩
    refine ⟨?_, ?_, ?_⟩
    · convert hpa.max hpc using 1
      funext x
      exact EReal.coe_strictMono.monotone.map_max
    · intro x hx
      exact ⟨(hba x hx).1.trans (le_max_left _ _),
        max_le (hba x hx).2 (hbc x hx).2⟩
    · rintro x ⟨hx, hp⟩
      rcases lt_max_iff.mp hp with ha | hc
      · exact hFa ⟨hx, ha⟩
      · exact hFc ⟨hx, hc⟩
  have hpoint : ∀ x ∈ F, ∃ j, x ∈ B j ∧ ∃ h ∈ H j, h x = 1 / 2 := by
    intro x hx
    obtain ⟨O, h, hO, hxO, hpsh, hvalue, hlo, hup, _hfo, hsub⟩ :=
      PlurifineSingleSuperlevelNeighborhoods.exists_bounded_single_superlevel
        hFine (show (⟨x, hFΩ hx⟩ : Ω) ∈ Subtype.val ⁻¹' F from hx)
    obtain ⟨v, ⟨j, rfl⟩, hxv, hvO⟩ := hbasis.exists_subset_of_mem_open hxO hO
    refine ⟨j, ⟨⟨x, hFΩ hx⟩, hxv, rfl⟩, h, ?_, hvalue⟩
    refine ⟨hpsh, ?_, ?_⟩
    · rintro z ⟨w, hw, rfl⟩
      exact ⟨hlo w.val w.2, hup w (hvO hw)⟩
    · rintro z ⟨⟨w, hw, rfl⟩, hp⟩
      exact hsub ⟨hvO hw, hp⟩
  have hseq : ∀ j, ∃ g : ℕ → ComplexModel n → ℝ,
      (∀ k, g k ∈ H j) ∧ (∀ x, Monotone (fun k ↦ g k x)) ∧
      uscRegularization (fun x ↦ ⨆ k, (g k x : EReal)) =
        uscRegularization (sSup ((fun h : ComplexModel n → ℝ ↦
          fun x ↦ (h x : EReal)) '' H j)) :=
    fun j ↦ exists_increasing_sequence (hne j) (hmax j)
  choose g hgmem hgmono hgeq using hseq
  let p : ℕ → ComplexModel n → EReal := fun j x ↦ ⨆ k, (g j k x : EReal)
  let Q : ℕ → ComplexModel n → EReal := fun j ↦ uscRegularization (p j)
  let G : ℕ → ℕ → Set (ComplexModel n) := fun j k ↦ {x | x ∈ B j ∧ 0 < g j k x}
  let E : Set (ComplexModel n) := F \ ⋃ j, ⋃ k, G j k
  let N : ℕ → Set (ComplexModel n) := fun j ↦ {x | x ∈ B j ∧ p j x < Q j x}
  have hgap (j : ℕ) (D : Opens (ComplexModel n)) (hDB : D ≤ B j) :
      relCapacity D {x | x ∈ D ∧ p j x < Q j x} = 0 :=
    (RegularizedIncreasingPshGapCapacityZero.regularized_isIncApprox_and_relCapacity_gap_eq_zero
      (hBΩ j) (g j) (fun k ↦ (hgmem j k).1) (fun x _ ↦ hgmono j x)
      (fun k ↦ (hgmem j k).2.1)).2.2.2 D hDB
  have hG (j k : ℕ) : G j k ⊆ F ∧ MeasurableSet (G j k) ∧
      IsOpen[PlurifinePshTopology.topology Ω] (Subtype.val ⁻¹' G j k) := by
    refine ⟨(hgmem j k).2.2, ?_, ?_⟩
    · simpa only [G, ← EReal.coe_zero, EReal.coe_lt_coe_iff] using
        FirstPass.MongeAmpere.measurableSet_psh_superlevel
          ((hgmem j k).1.mono (hBΩ j)) 0
    · let : TopologicalSpace Ω := PlurifinePshTopology.topology Ω
      change IsOpen[PlurifinePshTopology.topology Ω]
        ((Subtype.val ⁻¹' (B j : Set (ComplexModel n))) ∩
          {z : Ω | 0 < g j k z.val})
      exact (PlurifineEuclideanComparison.isOpen_euclidean (B j).isOpen).inter
        (PlurifinePshTopology.isOpen_realPsh_superlevel (hgmem j k).1 0)
  have hE : MeasurableSet E :=
    hFBorel.diff (MeasurableSet.iUnion fun j ↦ MeasurableSet.iUnion fun k ↦ (hG j k).2.1)
  have hEN : E ⊆ ⋃ j, N j := by
    rintro x ⟨hxF, hxP⟩
    obtain ⟨j, hxB, h, hh, hvalue⟩ := hpoint x hxF
    have hgzero : ∀ k, g j k x ≤ 0 := by
      intro k
      apply le_of_not_gt
      intro hp
      exact hxP (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨k, ⟨hxB, hp⟩⟩⟩)
    have hpzero : p j x ≤ (0 : EReal) :=
      iSup_le fun k ↦ EReal.coe_le_coe_iff.mpr (hgzero k)
    have hhQ : (h x : EReal) ≤ Q j x := by
      calc
        (h x : EReal) ≤ sSup ((fun h : ComplexModel n → ℝ ↦
            fun x ↦ (h x : EReal)) '' H j) x :=
          le_sSup (show (fun x ↦ (h x : EReal)) ∈
            (fun h : ComplexModel n → ℝ ↦ fun x ↦ (h x : EReal)) '' H j from
              ⟨h, hh, rfl⟩) x
        _ ≤ uscRegularization (sSup ((fun h : ComplexModel n → ℝ ↦
            fun x ↦ (h x : EReal)) '' H j)) x := le_uscRegularization _ x
        _ = Q j x := (congrFun (hgeq j) x).symm
    have hpos : (0 : EReal) < (h x : EReal) := by
      rw [hvalue]
      exact EReal.coe_lt_coe_iff.mpr (by norm_num : (0 : ℝ) < 1 / 2)
    exact mem_iUnion.mpr ⟨j, hxB, hpzero.trans_lt (hpos.trans_le hhQ)⟩
  refine ⟨B, g, hBΩ, fun j k ↦ (hgmem j k).1, fun j x _ ↦ hgmono j x,
    fun j k ↦ (hgmem j k).2.1, hG, hE, ?_⟩
  intro D _hDΩ
  refine le_antisymm (relCapacity_le_of_forall ?_) bot_le
  intro w hw hb
  let μ := Pending.MongeAmpere.canonicalBedfordTaylorMeasure D w hw
  have hμ : IsBTLimit D (fun _ ↦ w) μ := isBTLimit_canonicalBedfordTaylorMeasure hw
  have hz (j : ℕ) : μ (N j ∩ (D : Set (ComplexModel n))) = 0 := by
    have hset : N j ∩ (D : Set (ComplexModel n)) =
        {x | x ∈ B j ⊓ D ∧ p j x < Q j x} := by
      ext x
      change ((x ∈ B j ∧ p j x < Q j x) ∧ x ∈ D) ↔
        ((x ∈ B j ∧ x ∈ D) ∧ p j x < Q j x)
      tauto
    have hc : relCapacity (B j ⊓ D) (N j ∩ (D : Set (ComplexModel n))) = 0 := by
      rw [hset]
      exact hgap j (B j ⊓ D) inf_le_left
    have hbound : ∀ i : Fin n, ∀ x ∈ B j ⊓ D, |w x| ≤ (1 : ℝ) := by
      intro i x hx
      exact abs_le.mpr ⟨(hb x hx.2).1, (hb x hx.2).2.trans (by norm_num)⟩
    have hNU : N j ∩ (D : Set (ComplexModel n)) ⊆
        (B j ⊓ D : Opens (ComplexModel n)) := fun x hx ↦ ⟨hx.1.1, hx.2⟩
    refine le_antisymm ((hμ.le_relCapacity_of_abs_le (fun _ ↦ hw) inf_le_right
      (by norm_num : (0 : ℝ) < 1) hbound hNU).trans ?_) bot_le
    rw [hc, mul_zero]
  have hunion : μ (⋃ j, N j ∩ (D : Set (ComplexModel n))) = 0 := measure_iUnion_null hz
  have hsub : E ∩ (D : Set (ComplexModel n)) ⊆
      ⋃ j, N j ∩ (D : Set (ComplexModel n)) := by
    rintro x ⟨hxE, hxD⟩
    obtain ⟨j, hxj⟩ := mem_iUnion.mp (hEN hxE)
    exact mem_iUnion.mpr ⟨j, hxj, hxD⟩
  exact (measure_mono hsub).trans hunion.le

end SGPT.Foundations.Analysis.Pending.BorelPlurifineOpenCountableNormalizedSuperlevelCover
