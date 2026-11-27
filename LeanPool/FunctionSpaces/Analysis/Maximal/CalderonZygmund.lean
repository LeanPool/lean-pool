/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Maximal.DyadicCubes

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Calderón–Zygmund decomposition

Three general facts on means come first: `‖⨍ f‖ ≤ ⨍ ‖f‖` for every measure
(`MeasureTheory.enorm_average_le`) and, for a set `s` of finite measure,
`μ(s) ‖⨍_s f‖ ≤ ∫_s ‖f‖` (`MeasureTheory.measure_mul_enorm_setAverage_le`) and
`∫_s ‖f - ⨍_s f‖ ≤ 2 ∫_s ‖f‖` (`MeasureTheory.setLIntegral_enorm_sub_setAverage_le`).

For `G : V → [0, ∞]` and a height `t ∈ [0, ∞]`, a dyadic cube `Q` is **big** when the average
`⨍_Q G` exceeds `t` (`Rd.lt_setLAverage_zcell_iff`). The **maximal big cubes** (`Rd.czMaximal`)
are the big cubes whose strict ancestors are not big. They are pairwise disjoint
(`Rd.czMaximal_pairwiseDisjoint`), so every point lies in at most one of them
(`Rd.subsingleton_czMaximal_mem_zcell`), their averages lie in `(t, 2^n t]` (`Rd.cz_avg_gt`,
`Rd.cz_avg_le`), and their union `Ω` (`Rd.czSet`) has measure at most `t⁻¹ ∫ G`
(`Rd.cz_volume_le`). In dimension `n ≥ 1`, for `∫ G < ∞` and `0 < t`, cubes of large size have
average at most `t` (`Rd.exists_forall_setLAverage_zcell_sub_le`), so every big cube lies in a
maximal one (`Rd.exists_maximal_of_big`); for a.e.-measurable `G` with `∫ G < ∞` and `0 < t`,
`G ≤ t` almost everywhere outside `Ω` (`Rd.cz_ae_le_of_notMem`). The union of the closed balls of
radius `2n 2^(-k)` around the centres of the maximal cubes `Q_{k,m}`, twice the radius `n 2^(-k)`
of a ball around the centre containing
the cube, is the enlarged set `Ω*` (`Rd.czEnlarged`).
-/

@[expose] public section

open MeasureTheory Module Metric Set
open scoped ENNReal

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-! ### Means over a set -/

/-- The norm of a mean is at most the mean of the norm: `‖⨍ f dμ‖ ≤ ⨍ ‖f‖ dμ` in `[0, ∞]`, for
every function `f` with values in a real normed space. Both means are integrals for the
normalised measure `μ(α)⁻¹ μ`. -/
theorem enorm_average_le (f : α → E) : ‖⨍ x, f x ∂μ‖ₑ ≤ ⨍⁻ x, ‖f x‖ₑ ∂μ := by
  rw [average_eq', laverage_eq']
  exact eNorm_integral_le_lintegral_eNorm f

/-- `μ(s) ‖⨍_s f‖ ≤ ∫_s ‖f‖` for every set `s` of finite measure and every function `f` with
values in a real normed space, by `MeasureTheory.enorm_average_le` and Mathlib's
`measure_mul_setLAverage`. -/
theorem measure_mul_enorm_setAverage_le {s : Set α} (hs : μ s ≠ ∞) (f : α → E) :
    μ s * ‖⨍ x in s, f x ∂μ‖ₑ ≤ ∫⁻ x in s, ‖f x‖ₑ ∂μ :=
  (mul_le_mul_right (enorm_average_le f) _).trans_eq (measure_mul_setLAverage _ hs)

/-- **The mass of `f` minus its mean**: `∫_s ‖f - ⨍_s f‖ ≤ 2 ∫_s ‖f‖` for every set `s` of finite
measure and every function `f` with values in a real normed space, since
`‖f - ⨍_s f‖ ≤ ‖f‖ + ‖⨍_s f‖` and `μ(s) ‖⨍_s f‖ ≤ ∫_s ‖f‖`. -/
theorem setLIntegral_enorm_sub_setAverage_le {s : Set α} (hs : μ s ≠ ∞) (f : α → E) :
    ∫⁻ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ₑ ∂μ ≤ 2 * ∫⁻ x in s, ‖f x‖ₑ ∂μ :=
  calc ∫⁻ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ₑ ∂μ
      ≤ ∫⁻ x in s, (‖f x‖ₑ + ‖⨍ y in s, f y ∂μ‖ₑ) ∂μ := lintegral_mono fun _ => eNorm_sub_le
    _ = (∫⁻ x in s, ‖f x‖ₑ ∂μ) + μ s * ‖⨍ y in s, f y ∂μ‖ₑ := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, mul_comm]
    _ ≤ (∫⁻ x in s, ‖f x‖ₑ ∂μ) + ∫⁻ x in s, ‖f x‖ₑ ∂μ :=
        add_le_add le_rfl (measure_mul_enorm_setAverage_le hs f)
    _ = 2 * ∫⁻ x in s, ‖f x‖ₑ ∂μ := (two_mul _).symm

end MeasureTheory

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Big cubes -/

variable {G : V → ℝ≥0∞} {t : ℝ≥0∞}

/-- A height `t` lies below the average of `G` over a cube `Q` exactly when `t |Q| < ∫_Q G`. -/
theorem lt_setLAverage_zcell_iff (k : ℤ) (m : Fin (finrank ℝ V) → ℤ) :
    t < ⨍⁻ y in zcell k m, G y ∂volume ↔
      t * volume (zcell (V := V) k m) < ∫⁻ y in zcell k m, G y := by
  rw [setLAverage_eq]
  exact ENNReal.lt_div_iff_mul_lt (Or.inl (volume_zcell_pos k m).ne')
    (Or.inl (volume_zcell_lt_top k m).ne)

/-- **Coarse cubes are not big**: in dimension `n ≥ 1`, if `∫ G < ∞` and `0 < t`, then for every
level `k` there is a bound `B` such that every cube of level `k - l` with `l > B` has an average of
`G` at most `t`, since `t |Q| ≥ ∫ G` for all large cubes `Q`. -/
theorem exists_forall_setLAverage_zcell_sub_le [Nontrivial V] (hGi : ∫⁻ x, G x ≠ ∞)
    (ht0 : 0 < t) (k : ℤ) : ∃ B : ℕ, ∀ l : ℕ, B < l → ∀ m' : Fin (finrank ℝ V) → ℤ,
      ⨍⁻ y in zcell (k - l) m', G y ∂volume ≤ t := by
  rcases eq_or_ne t ∞ with rfl | ht
  · exact ⟨0, fun _ _ _ => le_top⟩
  have hc0 : volume (zcell (V := V) k 0) ≠ 0 := (volume_zcell_pos k 0).ne'
  have hct : volume (zcell (V := V) k 0) ≠ ∞ := (volume_zcell_lt_top k 0).ne
  have htc0 : t * volume (zcell (V := V) k 0) ≠ 0 := mul_ne_zero ht0.ne' hc0
  have htct : t * volume (zcell (V := V) k 0) ≠ ∞ := ENNReal.mul_ne_top ht hct
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hGi htc0)
  refine ⟨N, fun l hl m' => not_lt.1 fun hbig => ?_⟩
  rw [lt_setLAverage_zcell_iff, volume_zcell_sub k l 0 m'] at hbig
  have hGN := (ENNReal.div_lt_iff (Or.inl htc0) (Or.inl htct)).1 hN
  have hNl : (N : ℝ≥0∞) ≤ 2 ^ (l * finrank ℝ V) := by
    have hn : 0 < finrank ℝ V := finrank_pos
    have h : N ≤ 2 ^ (l * finrank ℝ V) := (hl.le.trans l.lt_two_pow_self.le).trans
      (Nat.pow_le_pow_right two_pos (Nat.le_mul_of_pos_right l hn))
    exact_mod_cast h
  have hlt : ∫⁻ x, G x < ∫⁻ x, G x :=
    calc ∫⁻ x, G x < N * (t * volume (zcell (V := V) k 0)) := hGN
      _ ≤ 2 ^ (l * finrank ℝ V) * (t * volume (zcell (V := V) k 0)) := by gcongr
      _ = t * (2 ^ (l * finrank ℝ V) * volume (zcell (V := V) k 0)) := by ring
      _ < ∫⁻ y in zcell (k - l) m', G y := hbig
      _ ≤ ∫⁻ x, G x := setLIntegral_le_lintegral _ _
  exact lt_irrefl _ hlt

/-! ### Maximal big cubes -/

/-- The **maximal big cubes** of `G` at height `t`: the pairs `(k, m)` such that the average of
`G` over the cube `Q_{k,m}` exceeds `t` while the average over every strict ancestor
`Q_{k-l, m^{(l)}}`, `l ≥ 1`, does not. -/
def czMaximal (G : V → ℝ≥0∞) (t : ℝ≥0∞) : Set (ℤ × (Fin (finrank ℝ V) → ℤ)) :=
  {km | t < ⨍⁻ y in zcell km.1 km.2, G y ∂volume ∧
    ∀ l : ℕ, 0 < l → ¬ t < ⨍⁻ y in zcell (km.1 - l) (cubeAncestor l km.2), G y ∂volume}

/-- **Every big cube lies in a maximal one**: in dimension `n ≥ 1`, if `∫ G < ∞`, `0 < t` and
the average of `G` over `Q_{k,m}` exceeds `t`, then for some `l ≥ 0` the ancestor
`Q_{k-l, m^{(l)}}` is a maximal big cube, and it contains `Q_{k,m}`. -/
theorem exists_maximal_of_big [Nontrivial V] (hGi : ∫⁻ x, G x ≠ ∞) (ht0 : 0 < t) {k : ℤ}
    {m : Fin (finrank ℝ V) → ℤ} (h : t < ⨍⁻ y in zcell k m, G y ∂volume) :
    ∃ l : ℕ, (k - l, cubeAncestor l m) ∈ czMaximal G t ∧
      zcell k m ⊆ zcell (k - l) (cubeAncestor l m) := by
  classical
  obtain ⟨B, hB⟩ := exists_forall_setLAverage_zcell_sub_le hGi ht0 k
  let P : ℕ → Prop := fun l => t < ⨍⁻ y in zcell (k - l) (cubeAncestor l m), G y ∂volume
  have hP0 : P 0 := by simpa [P, cubeAncestor] using h
  obtain ⟨l₀, hl₀⟩ : ∃ l₀, Nat.findGreatest P B = l₀ := ⟨_, rfl⟩
  have hspec : P l₀ := hl₀ ▸ Nat.findGreatest_spec (Nat.zero_le B) hP0
  refine ⟨l₀, ⟨hspec, fun l hl hbig => ?_⟩, ?_⟩
  · have hk : k - ((l₀ + l : ℕ) : ℤ) = k - l₀ - l := by push_cast; ring
    have hbig' : P (l₀ + l) := by
      change t < ⨍⁻ y in zcell (k - ((l₀ + l : ℕ) : ℤ)) (cubeAncestor (l₀ + l) m), G y ∂volume
      rwa [hk, add_comm, ← cubeAncestor_add]
    have hle : l₀ + l ≤ B := not_lt.1 fun hlt => (hB _ hlt _).not_gt hbig'
    have hmax := Nat.le_findGreatest hle hbig'
    rw [hl₀] at hmax
    omega
  · have hsub := zcell_subset_cubeAncestor (V := V) (k - l₀) l₀ m
    rwa [sub_add_cancel] at hsub

/-- Two distinct maximal big cubes `Q_{k,m}` and `Q_{k',m'}` with `k ≤ k'` are disjoint: if the
finer cube met the coarser one, the coarser one would be its ancestor, which is not big. -/
theorem czMaximal_disjoint_of_le {k k' : ℤ} {m m' : Fin (finrank ℝ V) → ℤ}
    (h : (k, m) ∈ czMaximal G t) (h' : (k', m') ∈ czMaximal G t) (hk : k ≤ k')
    (hne : (k, m) ≠ (k', m')) : Disjoint (zcell (V := V) k' m') (zcell k m) := by
  obtain ⟨l, rfl⟩ := Int.le.dest hk
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have hm : m' ≠ m := fun e => hne (by simp [e])
    simpa using zcell_disjoint (V := V) k hm
  · have hanc : cubeAncestor l m' ≠ m := by
      intro e
      have hnot := h'.2 l hl
      rw [add_sub_cancel_right, e] at hnot
      exact hnot h.1
    exact (zcell_disjoint k hanc).mono_left (zcell_subset_cubeAncestor k l m')

/-- The maximal big cubes are **pairwise disjoint**. -/
theorem czMaximal_pairwiseDisjoint :
    (czMaximal G t).PairwiseDisjoint (fun km => zcell (V := V) km.1 km.2) := by
  rintro ⟨k, m⟩ h ⟨k', m'⟩ h' hne
  rcases le_total k k' with hk | hk
  · exact (czMaximal_disjoint_of_le h h' hk hne).symm
  · exact czMaximal_disjoint_of_le h' h hk hne.symm

/-- Every point lies in **at most one maximal big cube**, since these cubes are disjoint
(Mathlib's `Set.PairwiseDisjoint.elim_set`). -/
theorem subsingleton_czMaximal_mem_zcell (x : V) :
    {km : czMaximal G t | x ∈ zcell (V := V) km.1.1 km.1.2}.Subsingleton :=
  fun a ha b hb => Subtype.ext (czMaximal_pairwiseDisjoint.elim_set a.2 b.2 x ha hb)

/-- There are countably many maximal big cubes. -/
theorem czMaximal_countable : (czMaximal G t).Countable :=
  (czMaximal G t).to_countable

/-- The average of `G` over a maximal big cube exceeds `t`. -/
theorem cz_avg_gt {k : ℤ} {m : Fin (finrank ℝ V) → ℤ} (h : (k, m) ∈ czMaximal G t) :
    t < ⨍⁻ y in zcell k m, G y ∂volume :=
  h.1

/-- The average of `G` over a maximal big cube is at most `2^n t`: the parent cube is not big and
has `2^n` times the volume. -/
theorem cz_avg_le {k : ℤ} {m : Fin (finrank ℝ V) → ℤ} (h : (k, m) ∈ czMaximal G t) :
    ⨍⁻ y in zcell k m, G y ∂volume ≤ 2 ^ finrank ℝ V * t := by
  have hpar : ¬ t < ⨍⁻ y in zcell (k - 1) (cubeParent m), G y ∂volume := by
    simpa [cubeAncestor] using h.2 1 one_pos
  rw [lt_setLAverage_zcell_iff, not_lt] at hpar
  have hvol := volume_zcell_cubeParent (V := V) (k - 1) m
  have hsub := zcell_succ_subset_cubeParent (V := V) (k - 1) m
  rw [sub_add_cancel] at hvol hsub
  rw [setLAverage_eq]
  refine ENNReal.div_le_of_le_mul ?_
  calc ∫⁻ y in zcell k m, G y ≤ ∫⁻ y in zcell (k - 1) (cubeParent m), G y := lintegral_mono_set hsub
    _ ≤ t * volume (zcell (V := V) (k - 1) (cubeParent m)) := hpar
    _ = 2 ^ finrank ℝ V * t * volume (zcell (V := V) k m) := by rw [hvol]; ring

/-- A maximal big cube `Q` has volume at most `t⁻¹ ∫_Q G`, for every height `t`, with
`0⁻¹ = ∞`: for `t = 0` the integral `∫_Q G` is positive and the bound is `∞`. -/
theorem cz_volume_zcell_le {k : ℤ} {m : Fin (finrank ℝ V) → ℤ} (h : (k, m) ∈ czMaximal G t) :
    volume (zcell (V := V) k m) ≤ t⁻¹ * ∫⁻ y in zcell k m, G y := by
  have hlt := (lt_setLAverage_zcell_iff k m).1 h.1
  rcases eq_or_ne t 0 with rfl | ht0
  · rw [zero_mul] at hlt
    rw [ENNReal.inv_zero, ENNReal.top_mul hlt.ne']
    exact le_top
  · exact (ENNReal.mul_le_iff_le_inv ht0 (ne_top_of_lt h.1)).1 hlt.le

/-! ### The exceptional set -/

/-- The **exceptional set** `Ω` of the Calderón–Zygmund decomposition: the union of the maximal
big cubes. -/
def czSet (G : V → ℝ≥0∞) (t : ℝ≥0∞) : Set V := ⋃ km ∈ czMaximal G t, zcell km.1 km.2

/-- The **enlarged exceptional set** `Ω*`: the union of the closed balls of radius `2n 2^(-k)`
around the centres of the maximal big cubes `Q_{k,m}`, twice the radius `n 2^(-k)` of a ball
around the centre containing the cube (`Rd.zcell_subset_closedBall`). -/
noncomputable def czEnlarged (G : V → ℝ≥0∞) (t : ℝ≥0∞) : Set V :=
  ⋃ km ∈ czMaximal G t, closedBall (zcellCenter km.1 km.2) (2 * (finrank ℝ V / 2 ^ km.1))

/-- The exceptional set is measurable. -/
theorem measurableSet_czSet : MeasurableSet (czSet G t) :=
  MeasurableSet.biUnion czMaximal_countable fun _ _ => measurableSet_zcell _ _

/-- The enlarged exceptional set is measurable. -/
theorem measurableSet_czEnlarged : MeasurableSet (czEnlarged G t) :=
  MeasurableSet.biUnion czMaximal_countable fun _ _ => measurableSet_closedBall

/-- Every maximal big cube lies in the exceptional set. -/
theorem zcell_subset_czSet {k : ℤ} {m : Fin (finrank ℝ V) → ℤ} (h : (k, m) ∈ czMaximal G t) :
    zcell k m ⊆ czSet G t :=
  subset_biUnion_of_mem (u := fun km : ℤ × (Fin (finrank ℝ V) → ℤ) => zcell km.1 km.2) h

/-- The exceptional set lies in the enlarged one: a cube `Q_{k,m}` lies in the closed ball of
radius `n 2^(-k)` around its centre. -/
theorem czSet_subset_czEnlarged : czSet G t ⊆ czEnlarged G t :=
  iUnion₂_mono fun km _ => (zcell_subset_closedBall _ _).trans
    (closedBall_subset_closedBall (le_mul_of_one_le_left (by positivity) one_le_two))

/-- **The measure of the exceptional set**: `|Ω| ≤ t⁻¹ ∫ G` for every height `t`, with
`0⁻¹ = ∞`, since every maximal cube `Q` has `|Q| ≤ t⁻¹ ∫_Q G` and the cubes are disjoint. -/
theorem cz_volume_le : volume (czSet G t) ≤ t⁻¹ * ∫⁻ x, G x := by
  rw [czSet, measure_biUnion czMaximal_countable czMaximal_pairwiseDisjoint
    fun _ _ => measurableSet_zcell _ _]
  calc ∑' km : czMaximal G t, volume (zcell (V := V) km.1.1 km.1.2)
      ≤ ∑' km : czMaximal G t, t⁻¹ * ∫⁻ y in zcell km.1.1 km.1.2, G y :=
        tsum_le_tsum fun km => cz_volume_zcell_le km.2
    _ = t⁻¹ * ∫⁻ y in czSet G t, G y := by
        rw [ENNReal.tsum_mul_left, czSet, lintegral_biUnion czMaximal_countable
          (fun _ _ => measurableSet_zcell _ _) czMaximal_pairwiseDisjoint]
    _ ≤ t⁻¹ * ∫⁻ x, G x := mul_le_mul_right (setLIntegral_le_lintegral _ _) _

/-- **`G ≤ t` off the exceptional set**: in dimension `n ≥ 1`, for an a.e.-measurable `G` with
finite integral and `0 < t`, almost every `x ∉ Ω` satisfies `G x ≤ t`. No dyadic cube containing
such an `x` is big, since it would lie in a maximal big cube, so Lebesgue differentiation along
dyadic cubes (`Rd.ae_le_of_forall_laverage_le`) applies. -/
theorem cz_ae_le_of_notMem [Nontrivial V] (hG : AEMeasurable G volume) (hGi : ∫⁻ x, G x ≠ ∞)
    (ht0 : 0 < t) : ∀ᵐ x, x ∉ czSet G t → G x ≤ t := by
  filter_upwards [ae_le_of_forall_laverage_le hG hGi t] with x hx hxΩ
  refine hx fun k => not_lt.1 fun hbig => hxΩ ?_
  obtain ⟨l, hmem, hsub⟩ := exists_maximal_of_big hGi ht0 hbig
  exact mem_biUnion hmem (hsub (mem_cubeAt _ x))

end Rd
