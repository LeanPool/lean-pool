/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTenThirdsFromSource
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

public section

open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace ESS

/-- On a finite-measure cylinder, convergence in measure on every member of
an increasing measurable exhaustion gives convergence in measure globally. -/
theorem blowup_tendstoInMeasure_of_local_exhaustion
    {α E : Type*} [MeasurableSpace α] [PseudoEMetricSpace E]
    (μ : Measure α) [IsFiniteMeasure μ]
    (S : ℕ → Set α) (hSm : ∀ n, MeasurableSet (S n))
    (hSmono : Monotone S) (hcover : μ (⋃ n, S n)ᶜ = 0)
    (f : ℕ → α → E) (g : α → E)
    (hlocal : ∀ n, TendstoInMeasure (μ.restrict (S n)) f atTop g) :
    TendstoInMeasure μ f atTop g := by
  let T : ℕ → Set α := fun n => (S n)ᶜ
  have hTm (n : ℕ) : NullMeasurableSet (T n) μ := (hSm n).compl.nullMeasurableSet
  have hTanti : Antitone T := fun i j hij => compl_subset_compl.mpr (hSmono hij)
  have hTinter : μ (⋂ n, T n) = 0 := by
    simpa only [T, ← Set.compl_iUnion] using hcover
  have hTzero : Tendsto (fun n => μ (T n)) atTop (nhds 0) := by
    have h := tendsto_measure_iInter_atTop hTm hTanti
      ⟨0, (measure_ne_top μ (T 0))⟩
    change Tendsto (μ ∘ T) atTop (nhds 0)
    simpa only [hTinter] using h
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hδhalf : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  have htail : ∀ᶠ n in atTop, μ (T n) ≤ δ / 2 :=
    (ENNReal.tendsto_nhds_zero.mp hTzero) (δ / 2) hδhalf
  obtain ⟨n, hn⟩ := htail.exists
  have hinside : ∀ᶠ k in atTop,
      (μ.restrict (S n)) {x | ε ≤ edist (f k x) (g x)} ≤ δ / 2 :=
    (ENNReal.tendsto_nhds_zero.mp (hlocal n ε hε)) (δ / 2) hδhalf
  filter_upwards [hinside] with k hk
  let B := {x | ε ≤ edist (f k x) (g x)}
  have hBsubset : B ⊆ (B ∩ S n) ∪ T n := by
    intro x hx
    by_cases hxs : x ∈ S n
    · exact Or.inl ⟨hx, hxs⟩
    · exact Or.inr hxs
  calc
    μ B ≤ μ ((B ∩ S n) ∪ T n) := measure_mono hBsubset
    _ ≤ μ (B ∩ S n) + μ (T n) := measure_union_le _ _
    _ ≤ (μ.restrict (S n)) B + μ (T n) := by
      simpa only [add_comm] using
        (add_le_add_right (Measure.le_restrict_apply (S n) B) (μ (T n)))
    _ ≤ δ / 2 + δ / 2 := add_le_add hk hn
    _ ≤ δ := by simp

/-- Convergence in measure on every finite past subcylinder extends to the
open cylinder ending at time zero. -/
theorem blowup_tendstoInMeasure_to_time_zero
    {E : Type*} [PseudoEMetricSpace E]
    (A : Set CKN.Foundation.Parabolic.Vec3) (hA : MeasurableSet A)
    (hAfin : volume A < ⊤) (a : ℝ)
    (f : ℕ → CKN.Foundation.Parabolic.Vec3 × ℝ → E)
    (g : CKN.Foundation.Parabolic.Vec3 × ℝ → E)
    (hlocal : ∀ b : ℝ, b < 0 →
      TendstoInMeasure
        ((volume.prod volume).restrict (A ×ˢ Ioo a b)) f atTop g) :
    TendstoInMeasure ((volume.prod volume).restrict (A ×ˢ Ioo a 0)) f atTop g := by
  let topBox := A ×ˢ Ioo a 0
  let μ : Measure (CKN.Foundation.Parabolic.Vec3 × ℝ) :=
    (volume.prod volume).restrict topBox
  let b : ℕ → ℝ := fun n => -(1 / ((n : ℝ) + 1))
  let S : ℕ → Set (CKN.Foundation.Parabolic.Vec3 × ℝ) :=
    fun n => A ×ˢ Ioo a (b n)
  have hbneg (n : ℕ) : b n < 0 := by dsimp [b]; exact neg_neg_of_pos (by positivity)
  have hb0 : Tendsto b atTop (nhds 0) := by
    simpa only [b, neg_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  have hSmeas (n : ℕ) : MeasurableSet (S n) := hA.prod measurableSet_Ioo
  have hSsub (n : ℕ) : S n ⊆ topBox := by
    intro z hz
    exact ⟨hz.1, hz.2.1, lt_trans hz.2.2 (hbneg n)⟩
  have hbmono : Monotone b := by
    intro m n hmn
    dsimp [b]
    apply neg_le_neg
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hSmono : Monotone S := by
    intro m n hmn z hz
    exact ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 (hbmono hmn)⟩
  have hunion : (⋃ n, S n) = topBox := by
    ext z
    constructor
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨n, hz⟩
      exact hSsub n hz
    · intro hz
      have hev := hb0.eventually (eventually_gt_nhds hz.2.2)
      obtain ⟨n, hn⟩ := hev.exists
      exact Set.mem_iUnion.mpr ⟨n, ⟨hz.1, hz.2.1, hn⟩⟩
  have hcover : μ (⋃ n, S n)ᶜ = 0 := by
    rw [hunion]
    have htop : MeasurableSet topBox := hA.prod measurableSet_Ioo
    rw [show μ topBoxᶜ = (volume.prod volume : Measure
      (CKN.Foundation.Parabolic.Vec3 × ℝ))
      (topBoxᶜ ∩ topBox) by exact Measure.restrict_apply htop.compl]
    simp
  have hμfin : IsFiniteMeasure μ := by
    apply isFiniteMeasure_restrict.mpr
    change (volume.prod volume : Measure (CKN.Foundation.Parabolic.Vec3 × ℝ))
      topBox ≠ ⊤
    rw [Measure.prod_prod]
    exact (ENNReal.mul_lt_top hAfin (by simp : volume (Ioo a 0) < ⊤)).ne
  have hfinite : IsFiniteMeasure μ := hμfin
  have hμeq (n : ℕ) : μ.restrict (S n) =
      (volume.prod volume).restrict (S n) := by
    rw [show μ = (volume.prod volume).restrict topBox by rfl,
      Measure.restrict_restrict (hSmeas n), inter_eq_left.mpr (hSsub n)]
  apply blowup_tendstoInMeasure_of_local_exhaustion μ S hSmeas hSmono hcover f g
  intro n
  rw [hμeq]
  exact hlocal (b n) (hbneg n)

/-- Strong local `L²` convergence below time zero implies convergence in
measure on the full bounded open past cylinder. -/
theorem blowup_tendstoInMeasure_to_time_zero_of_local_Ltwo
    (A : Set CKN.Foundation.Parabolic.Vec3) (hA : MeasurableSet A)
    (hAfin : volume A < ⊤) (a : ℝ)
    (f : ℕ → CKN.Foundation.Parabolic.Vec3 × ℝ →
      CKN.Foundation.Parabolic.Vec3)
    (g : CKN.Foundation.Parabolic.Vec3 × ℝ →
      CKN.Foundation.Parabolic.Vec3)
    (hlocal : ∀ b : ℝ, b < 0 →
      Tendsto (fun k => eLpNorm (fun z => f k z - g z) 2
        ((volume.prod volume).restrict (A ×ˢ Ioo a b)))
        atTop (nhds 0)) :
    TendstoInMeasure ((volume.prod volume).restrict (A ×ˢ Ioo a 0))
      f atTop g := by
  apply blowup_tendstoInMeasure_to_time_zero A hA hAfin a f g
  intro b hb
  exact tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (hlocal b hb)

end ESS
