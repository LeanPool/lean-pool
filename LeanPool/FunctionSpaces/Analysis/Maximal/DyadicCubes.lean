/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Maximal.DyadicGrid
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Volume and nesting of dyadic cubes

The dyadic cube `Q_{k,m} = {x : ⌊2^k x_i⌋ = m_i for all i}` of level `k ∈ ℤ` (`Rd.zcell`) is a
box in the coordinates of `Rd.gridBasis` (`Rd.zcell_eq_preimage`) and has the volume `2^(-kn)`
(`Rd.volume_zcell`). Cubes are **nested**: each cube of level `k + 1` lies in its parent of
level `k` (`Rd.zcell_succ_subset_cubeParent`), so two cubes are nested or disjoint
(`Rd.zcell_subset_or_disjoint`).

**Lebesgue differentiation along cubes**: for a locally integrable `F`, the averages of `F` over
the cube of level `k` containing `x` tend to `F x` as `k → ∞` for almost every `x`
(`Rd.ae_tendsto_average_cubeAt`), since every such cube lies in a ball of comparable volume
around a nearby centre and averages over a subset are controlled by averages over the larger set
(`Rd.abs_setAverage_sub_le`). Consequently an integrable `G ≥ 0` whose cube averages at `x` are
all at most `t` satisfies `G x ≤ t` almost everywhere (`Rd.ae_le_of_forall_laverage_le`).
-/

@[expose] public section

open MeasureTheory Module Metric Filter Set
open scoped ENNReal Topology

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Volume -/

section Measure

variable [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace V] [BorelSpace V] in
/-- In coordinates, the cube `Q_{k,m}` is the box `∏_i [m_i 2^(-k), (m_i + 1) 2^(-k))`. -/
theorem zcell_eq_preimage (k : ℤ) (m : Fin (finrank ℝ V) → ℤ) :
    zcell k m = (fun x : V => WithLp.ofLp ((gridBasis V).repr x)) ⁻¹'
      Set.pi univ (fun i => Ico ((m i : ℝ) / 2 ^ k) (((m i : ℝ) + 1) / 2 ^ k)) := by
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  ext x
  simp only [zcell, zcellIndex, mem_ofPred_eq, mem_preimage, mem_univ_pi, mem_Ico, funext_iff,
    Int.floor_eq_iff, div_le_iff₀ hpos, lt_div_iff₀ hpos]
  refine forall_congr' fun i => ?_
  rw [mul_comm ((gridBasis V).repr x i)]

/-- **The volume of a cube**: `|Q_{k,m}| = 2^(-kn)`. -/
theorem volume_zcell (k : ℤ) (m : Fin (finrank ℝ V) → ℤ) :
    volume (zcell (V := V) k m) = ENNReal.ofReal ((2 : ℝ) ^ k)⁻¹ ^ finrank ℝ V := by
  have hmp : MeasurePreserving (fun x : V => WithLp.ofLp ((gridBasis V).repr x)) volume volume :=
    (PiLp.volume_preserving_ofLp _).comp (gridBasis V).measurePreserving_repr
  have hlen : ∀ i, ((m i : ℝ) + 1) / 2 ^ k - m i / 2 ^ k = ((2 : ℝ) ^ k)⁻¹ := fun i => by
    field_simp
    ring
  rw [zcell_eq_preimage, hmp.measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet, Real.volume_pi_Ico]
  simp only [hlen, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Cubes have positive volume. -/
theorem volume_zcell_pos (k : ℤ) (m : Fin (finrank ℝ V) → ℤ) :
    0 < volume (zcell (V := V) k m) := by
  rw [volume_zcell]
  exact ENNReal.pow_pos (ENNReal.ofReal_pos.2 (by positivity)) _

/-- Cubes have finite volume. -/
theorem volume_zcell_lt_top (k : ℤ) (m : Fin (finrank ℝ V) → ℤ) :
    volume (zcell (V := V) k m) < ∞ := by
  rw [volume_zcell]
  exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top

/-- The real volume of a cube is `2^(-kn)`. -/
theorem volume_real_zcell (k : ℤ) (m : Fin (finrank ℝ V) → ℤ) :
    volume.real (zcell (V := V) k m) = (((2 : ℝ) ^ k)⁻¹) ^ finrank ℝ V := by
  rw [measureReal_def, volume_zcell, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]

/-- The cells of level `j ∈ ℕ` have volume `2^(-jn)`. -/
theorem volume_cell (j : ℕ) (m : Fin (finrank ℝ V) → ℤ) :
    volume (cell (V := V) j m) = ENNReal.dyadicWeight (-(finrank ℝ V : ℝ)) j := by
  rw [← zcell_natCast, volume_zcell, zpow_natCast, ← one_div,
    ← ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_one_div_two_pow_pow]

end Measure

/-! ### Nesting -/

/-- The index of the **parent** cube: `⌊m_i / 2⌋` in every coordinate. -/
def cubeParent (m : Fin (finrank ℝ V) → ℤ) : Fin (finrank ℝ V) → ℤ := fun i => m i / 2

/-- Every cube of level `k + 1` lies in its parent of level `k`. -/
theorem zcell_succ_subset_cubeParent (k : ℤ) (m : Fin (finrank ℝ V) → ℤ) :
    zcell (V := V) (k + 1) m ⊆ zcell k (cubeParent m) := by
  intro x hx
  funext i
  have hm : ⌊(2 : ℝ) ^ (k + 1) * (gridBasis V).repr x i⌋ = m i := congrFun hx i
  have h2 : (2 : ℝ) ^ k * (gridBasis V).repr x i =
      (2 : ℝ) ^ (k + 1) * (gridBasis V).repr x i / ((2 : ℕ) : ℝ) := by
    rw [zpow_add_one₀ two_ne_zero]
    push_cast
    ring
  change ⌊(2 : ℝ) ^ k * (gridBasis V).repr x i⌋ = m i / 2
  rw [h2, Int.floor_div_natCast, hm]
  rfl

/-- The index of the ancestor `l` levels up: the parent map iterated `l` times. -/
def cubeAncestor (l : ℕ) (m : Fin (finrank ℝ V) → ℤ) : Fin (finrank ℝ V) → ℤ := cubeParent^[l] m

omit [FiniteDimensional ℝ V] in
/-- Ancestors of ancestors are ancestors. -/
theorem cubeAncestor_add (l l' : ℕ) (m : Fin (finrank ℝ V) → ℤ) :
    cubeAncestor l (cubeAncestor l' m) = cubeAncestor (l + l') m :=
  (Function.iterate_add_apply cubeParent l l' m).symm

/-- Every cube of level `k + l` lies in its ancestor of level `k`. -/
theorem zcell_subset_cubeAncestor (k : ℤ) (l : ℕ) (m : Fin (finrank ℝ V) → ℤ) :
    zcell (V := V) (k + l) m ⊆ zcell k (cubeAncestor l m) := by
  induction l generalizing k with
  | zero => simp [cubeAncestor]
  | succ l ih =>
    have hk : k + ((l + 1 : ℕ) : ℤ) = (k + 1) + l := by push_cast; ring
    rw [hk, cubeAncestor, Function.iterate_succ_apply']
    exact (ih (k + 1)).trans (zcell_succ_subset_cubeParent k _)

/-- The index of level `k - l` is the ancestor of the index of level `k`. -/
theorem zcellIndex_sub_cubeAncestor (k : ℤ) (l : ℕ) (x : V) :
    zcellIndex (k - l) x = cubeAncestor l (zcellIndex k x) := by
  have hx : x ∈ zcell ((k - l) + l) (zcellIndex k x) := by
    rw [sub_add_cancel]
    exact mem_zcell_zcellIndex k x
  exact zcell_subset_cubeAncestor (k - l) l _ hx

/-- **Nested or disjoint**: for `k ≤ k'`, the cube `Q_{k',m'}` lies in the cube `Q_{k,m}` or is
disjoint from it. -/
theorem zcell_subset_or_disjoint {k k' : ℤ} (hk : k ≤ k') (m m' : Fin (finrank ℝ V) → ℤ) :
    zcell (V := V) k' m' ⊆ zcell k m ∨ Disjoint (zcell (V := V) k' m') (zcell k m) := by
  obtain ⟨l, hl⟩ := Int.le.dest hk
  have hsub := zcell_subset_cubeAncestor (V := V) k l m'
  rw [hl] at hsub
  by_cases h : cubeAncestor l m' = m
  · exact Or.inl (h ▸ hsub)
  · exact Or.inr ((zcell_disjoint k h).mono_left hsub)

section Measure

variable [MeasurableSpace V] [BorelSpace V]

/-- The parent cube has `2^n` times the volume of its child. -/
theorem volume_zcell_cubeParent (k : ℤ) (m : Fin (finrank ℝ V) → ℤ) :
    volume (zcell (V := V) k (cubeParent m)) =
      2 ^ finrank ℝ V * volume (zcell (V := V) (k + 1) m) := by
  rw [volume_zcell, volume_zcell, ← mul_pow]
  congr 1
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), zpow_add_one₀ two_ne_zero]
  congr 1
  field_simp

/-- **Coarser cubes are larger**: a cube of level `k - l` has `2^(ln)` times the volume of a cube
of level `k`, for all indices. -/
theorem volume_zcell_sub (k : ℤ) (l : ℕ) (m m' : Fin (finrank ℝ V) → ℤ) :
    volume (zcell (V := V) (k - l) m') = 2 ^ (l * finrank ℝ V) * volume (zcell (V := V) k m) := by
  have h : ((2 : ℝ) ^ (k - l))⁻¹ = 2 ^ l * ((2 : ℝ) ^ k)⁻¹ := by
    rw [zpow_sub₀ two_ne_zero, zpow_natCast]
    field_simp
  rw [volume_zcell, volume_zcell, h, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, mul_pow, ← pow_mul]

end Measure

/-! ### Lebesgue differentiation along cubes -/

/-- The dyadic cube of level `k` containing `x`. -/
noncomputable def cubeAt (k : ℤ) (x : V) : Set V := zcell k (zcellIndex k x)

/-- Every point lies in its cube. -/
theorem mem_cubeAt (k : ℤ) (x : V) : x ∈ cubeAt k x := mem_zcell_zcellIndex k x

/-- **Averages over a subset**: if `Q ⊆ B` with `0 < |Q|` and `|B| < ∞`, and `F` is integrable
on `B`, then `|⨍_Q F - c| ≤ (|B| / |Q|) ⨍_B |F - c|` for every constant `c`. -/
theorem abs_setAverage_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {Q B : Set α}
    (hQB : Q ⊆ B) (hQ0 : μ Q ≠ 0) (hB : μ B ≠ ∞) {F : α → ℝ} (hF : IntegrableOn F B μ) (c : ℝ) :
    |(⨍ y in Q, F y ∂μ) - c| ≤ μ.real B / μ.real Q * ⨍ y in B, |F y - c| ∂μ := by
  have hQ : μ Q ≠ ∞ := ne_top_of_le_ne_top hB (measure_mono hQB)
  have hQr : 0 < μ.real Q := ENNReal.toReal_pos hQ0 hQ
  have hFQ : IntegrableOn F Q μ := hF.mono_set hQB
  have hsub : (⨍ y in Q, F y ∂μ) - c = (μ.real Q)⁻¹ * ∫ y in Q, (F y - c) ∂μ := by
    rw [setAverage_eq, integral_sub hFQ (integrableOn_const hQ), setIntegral_const, smul_eq_mul,
      smul_eq_mul]
    field_simp
  have hint : IntegrableOn (fun y => |F y - c|) B μ :=
    (hF.sub (integrableOn_const hB)).abs
  have hBr : 0 < μ.real B := ENNReal.toReal_pos (fun h => hQ0 (measure_mono_null hQB h)) hB
  have hrhs : μ.real B / μ.real Q * ⨍ y in B, |F y - c| ∂μ =
      (μ.real Q)⁻¹ * ∫ y in B, |F y - c| ∂μ := by
    rw [setAverage_eq, smul_eq_mul]
    field_simp
  rw [hsub, abs_mul, abs_of_pos (inv_pos.2 hQr), hrhs]
  gcongr
  calc |∫ y in Q, (F y - c) ∂μ| ≤ ∫ y in Q, |F y - c| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ y in B, |F y - c| ∂μ :=
        setIntegral_mono_set hint (Eventually.of_forall fun _ => abs_nonneg _)
          (Eventually.of_forall hQB)

/-- The cube of level `k` containing `x` lies in the closed ball of radius `(n+1) 2^(-k)` around
its centre. -/
theorem cubeAt_subset_closedBall (k : ℤ) (x : V) :
    cubeAt k x ⊆
      closedBall (zcellCenter k (zcellIndex k x)) (((finrank ℝ V : ℝ) + 1) / 2 ^ k) := by
  intro y hy
  rw [mem_closedBall, dist_eq_norm]
  refine (norm_sub_zcellCenter_le hy).trans ?_
  gcongr
  linarith

variable [MeasurableSpace V] [BorelSpace V]

/-- The closed ball of radius `(n+1) 2^(-k)` around the centre of the cube of level `k`
containing `x` has `(n+1)^n |B(0,1)|` times the volume of that cube. -/
theorem volume_real_closedBall_div_cubeAt (k : ℤ) (x : V) :
    volume.real (closedBall (zcellCenter k (zcellIndex k x))
        (((finrank ℝ V : ℝ) + 1) / 2 ^ k)) / volume.real (cubeAt k x) =
      ((finrank ℝ V : ℝ) + 1) ^ finrank ℝ V * volume.real (ball (0 : V) 1) := by
  rw [cubeAt, volume_real_zcell, Measure.addHaar_real_closedBall _ _ (by positivity),
    div_pow, inv_pow]
  field_simp

/-- **Lebesgue differentiation along dyadic cubes**: for a locally integrable `F`, almost every
`x` satisfies `⨍_{Q_k(x)} F → F x` as `k → ∞`, where `Q_k(x)` is the cube of level `k`
containing `x`. -/
theorem ae_tendsto_average_cubeAt {F : V → ℝ} (hF : LocallyIntegrable F volume) :
    ∀ᵐ x, Tendsto (fun k : ℕ => ⨍ y in cubeAt (k : ℤ) x, F y) atTop (𝓝 (F x)) := by
  have hae := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (μ := volume) hF 1
  filter_upwards [hae] with x hx
  have hδ : Tendsto (fun k : ℕ => ((finrank ℝ V : ℝ) + 1) / 2 ^ (k : ℤ)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mem_Ioi.2 (by positivity)⟩
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul ((finrank ℝ V : ℝ) + 1)
    rw [mul_zero] at h
    refine h.congr fun k => ?_
    rw [zpow_natCast, one_div, inv_pow, div_eq_mul_inv]
  have hmem : ∀ᶠ k : ℕ in atTop, x ∈ closedBall (zcellCenter (k : ℤ) (zcellIndex (k : ℤ) x))
      (1 * (((finrank ℝ V : ℝ) + 1) / 2 ^ (k : ℤ))) :=
    Eventually.of_forall fun k => by
      rw [one_mul]
      exact cubeAt_subset_closedBall (k : ℤ) x (mem_cubeAt _ x)
  have hlim := (hx (fun k : ℕ => zcellCenter (k : ℤ) (zcellIndex (k : ℤ) x)) _ hδ hmem).const_mul
    (((finrank ℝ V : ℝ) + 1) ^ finrank ℝ V * volume.real (ball (0 : V) 1))
  rw [mul_zero] at hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hlim
  rw [Real.norm_eq_abs, ← volume_real_closedBall_div_cubeAt (k : ℤ) x]
  simp only [Real.norm_eq_abs]
  exact abs_setAverage_sub_le (cubeAt_subset_closedBall (k : ℤ) x)
    (volume_zcell_pos _ _).ne' measure_closedBall_lt_top.ne
    (hF.integrableOn_isCompact (isCompact_closedBall _ _)) (F x)

/-- For an a.e.-measurable `G : α → ℝ≥0∞` with finite integral over `s`, the average of `G`
over `s` is `ENNReal.ofReal` of the average of the real function `G.toReal` (Mathlib's
`toReal_setLAverage`). -/
theorem setLAverage_eq_ofReal_setAverage {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G : α → ℝ≥0∞} {s : Set α} (hG : AEMeasurable G (μ.restrict s))
    (hGs : ∫⁻ x in s, G x ∂μ ≠ ∞) :
    ⨍⁻ x in s, G x ∂μ = ENNReal.ofReal (⨍ x in s, (G x).toReal ∂μ) := by
  rw [← toReal_setLAverage hG ((ae_lt_top' hG hGs).mono fun _ h => h.ne),
    ENNReal.ofReal_toReal (setLAverage_lt_top hGs).ne]

/-- **Pointwise bounds from cube averages**: if `G : V → ℝ≥0∞` is a.e.-measurable with finite
integral, then for every `t` and almost every `x`, `⨍_{Q_k(x)} G ≤ t` for all levels `k ∈ ℕ`
implies `G x ≤ t`. -/
theorem ae_le_of_forall_laverage_le {G : V → ℝ≥0∞} (hG : AEMeasurable G volume)
    (hGi : ∫⁻ x, G x ≠ ∞) (t : ℝ≥0∞) :
    ∀ᵐ x, (∀ k : ℕ, ⨍⁻ y in cubeAt (k : ℤ) x, G y ∂volume ≤ t) → G x ≤ t := by
  have hF : LocallyIntegrable (fun x => (G x).toReal) volume :=
    (integrable_toReal_of_lintegral_ne_top hG hGi).locallyIntegrable
  filter_upwards [ae_tendsto_average_cubeAt hF, ae_lt_top' hG hGi] with x hx hxt hle
  rw [← ENNReal.ofReal_toReal hxt.ne]
  refine le_of_tendsto' (ENNReal.tendsto_ofReal hx) fun k => ?_
  rw [← setLAverage_eq_ofReal_setAverage (s := cubeAt (k : ℤ) x) hG.restrict
    (ne_top_of_le_ne_top hGi (setLIntegral_le_lintegral _ G))]
  exact hle k

end Rd
