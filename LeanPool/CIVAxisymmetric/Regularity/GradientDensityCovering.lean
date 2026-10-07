/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.EnergyClassLemmas
public import LeanPool.CIVAxisymmetric.Regularity.EnergyIntegrable
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# The spatial Vitali covering step of the statement `CIV.timeZeroSingularSetNull`

This file proves the spatial analogue of Caffarelli–Kohn–Nirenberg's covering step
`step:thmC-covering`: if a set `S` of spatial points carries a uniform lower bound `ε r` on
the finite Dirichlet integral `∫⁻ |∇u|²` of backward parabolic cylinders `B(x, r) × (-r², 0)`
at arbitrarily small radii, then `S ∩ B(1)` has one-dimensional Hausdorff measure zero. The
route covers `S ∩ B(1)` at each scale by a disjoint (Vitali) subfamily of such cylinders,
compares the sum of the lower bounds against the finite integral over a shrinking backward
time slab, and lets the scale tend to zero.
-/

public section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The `sup`-norm extended diameter of a Euclidean spatial ball `vec3Ball x r` is at most
`2 r`: for two points of the ball, the Euclidean triangle inequality bounds their Euclidean
separation by `2 r`, and the `sup` norm used by the ambient metric on `Vec3` (the type's
default `Fin 3 → ℝ` norm) is dominated by the Euclidean norm. -/
private lemma ediam_vec3Ball_le (x : Vec3) (r : ℝ) :
    Metric.ediam (vec3Ball x r) ≤ ENNReal.ofReal (2 * r) := by
  refine Metric.ediam_le (fun y hy y' hy' => ?_)
  have hyx : vec3EuclideanNorm (y - x) < r := hy
  have hy'x : vec3EuclideanNorm (y' - x) < r := hy'
  have hyy' : vec3EuclideanNorm (y - y') < 2 * r := by
    have heq : y - y' = (y - x) + (x - y') := by abel
    have hxy' : vec3EuclideanNorm (x - y') = vec3EuclideanNorm (y' - x) := by
      rw [show x - y' = -(y' - x) by abel, vec3EuclideanNorm_neg]
    calc vec3EuclideanNorm (y - y')
        ≤ vec3EuclideanNorm (y - x) + vec3EuclideanNorm (x - y') := by
          rw [heq]; exact vec3EuclideanNorm_add_le _ _
      _ = vec3EuclideanNorm (y - x) + vec3EuclideanNorm (y' - x) := by rw [hxy']
      _ < r + r := add_lt_add hyx hy'x
      _ = 2 * r := by ring
  have hnorm : ‖y - y'‖ ≤ 2 * r := (norm_le_vec3EuclideanNorm (y - y')).trans hyy'.le
  rw [edist_eq_enorm_sub, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hnorm

private theorem vec3Ball_subset_unitBall_of_radius_lt_margin {x : Vec3} {r : ℝ}
    (hr : r < 1 - vec3EuclideanNorm x) : vec3Ball x r ⊆ vec3Ball (0 : Vec3) 1 := by
  intro y hy
  have hy' : vec3EuclideanNorm (y - x) < r := hy
  change vec3EuclideanNorm (y - 0) < 1
  rw [sub_zero]
  have htri : vec3EuclideanNorm y ≤ vec3EuclideanNorm (y - x) + vec3EuclideanNorm x := by
    have heq : y = (y - x) + x := by abel
    calc vec3EuclideanNorm y = vec3EuclideanNorm ((y - x) + x) := by rw [← heq]
      _ ≤ vec3EuclideanNorm (y - x) + vec3EuclideanNorm x := vec3EuclideanNorm_add_le _ _
  linarith only [htri, hy', hr]

private theorem mem_vec3Ball_enlargement_of_intersection (a b w : Vec3) (ra rb : ℝ)
    (hwa' : vec3EuclideanNorm (w - a) < ra) (hwb' : vec3EuclideanNorm (w - b) < rb)
    (hrad : ra ≤ 4 * rb) : a ∈ vec3Ball b (5 * rb) := by
  have htri : vec3EuclideanNorm (a - b) < ra + rb := by
    have heq : a - b = (a - w) + (w - b) := by abel
    have hswap : vec3EuclideanNorm (a - w) = vec3EuclideanNorm (w - a) := by
      rw [show a - w = -(w - a) by abel, vec3EuclideanNorm_neg]
    calc vec3EuclideanNorm (a - b)
        ≤ vec3EuclideanNorm (a - w) + vec3EuclideanNorm (w - b) := by
          rw [heq]; exact vec3EuclideanNorm_add_le _ _
      _ = vec3EuclideanNorm (w - a) + vec3EuclideanNorm (w - b) := by rw [hswap]
      _ < ra + rb := add_lt_add hwa' hwb'
  change vec3EuclideanNorm (a - b) < 5 * rb
  linarith only [htri, hrad]

private theorem countable_of_positive_disjoint_integrals {ι : Type*}
    (F : ParabolicPoint → ℝ≥0∞) (A : ι → Set ParabolicPoint) (E : Set ParabolicPoint)
    (g : ι → ℝ≥0∞) (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (hmeas : ∀ i, MeasurableSet (A i)) (hsub : ∀ i, A i ⊆ E)
    (hbound : ∀ i, g i ≤ ∫⁻ w in A i, F w) (hpos : ∀ i, g i ≠ 0)
    (hfin : (∫⁻ w in E, F w) < ⊤) : Countable ι := by
  classical
  have hsum_le : (∑' i, g i) ≤ ∫⁻ w in E, F w := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    have hd : Set.PairwiseDisjoint (↑s : Set ι) A := fun i _ j _ hij => hdisj hij
    calc (∑ i ∈ s, g i) ≤ ∑ i ∈ s, ∫⁻ w in A i, F w :=
          Finset.sum_le_sum fun i _ => hbound i
      _ = ∫⁻ w in ⋃ i ∈ s, A i, F w :=
          (lintegral_biUnion_finset hd (fun i _ => hmeas i) F).symm
      _ ≤ ∫⁻ w in E, F w := lintegral_mono_set (Set.iUnion₂_subset fun i _ => hsub i)
  have hsumne : (∑' i, g i) ≠ ⊤ := (hsum_le.trans_lt hfin).ne
  have hsupport : Function.support g = Set.univ := by
    ext i
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact hpos i
  have hcnt := Summable.countable_support_ennreal hsumne
  rw [hsupport] at hcnt
  exact Set.countable_univ_iff.mp hcnt

private theorem inverse_successor_scale_bounds :
    (∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1) ∧
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds (0 : ℝ)) := by
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδdef : δ = fun n : ℕ => 1 / ((n : ℝ) + 1) := rfl
  have hδpos : ∀ n : ℕ, 0 < δ n := by
    intro n; rw [hδdef]; positivity
  have hδle1 : ∀ n : ℕ, δ n ≤ 1 := by
    intro n
    rw [hδdef, div_le_one (by positivity)]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith only [hn0]
  have hδtendsto0 : Tendsto δ atTop (nhds (0 : ℝ)) := by
    rw [hδdef]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  exact ⟨hδpos, hδle1, hδtendsto0⟩

/-- **Spatial Vitali covering lemma** (the spatial analogue of CKN's
`step:thmC-covering`). If `S ⊆ Vec3` carries, at every point `x ∈ S` and every scale `r₀ > 0`,
a radius `r < r₀` with `ε r ≤ ∫_{B(x,r) × (-r²,0)} |∇u|²` (the same integrand and measure
`lintegral_gradSq_lt_top` produces: `‖Du z‖ₑ ^ (2:ℝ)` over the plain product-space `volume`
measure, restricted to the stated set), and the total `∫_{Q} |∇u|²` over the unit cylinder is
finite, then `S ∩ B(1)` has one-dimensional Hausdorff measure zero.

The proof fixes a scale `δ n = 1/(n+1) → 0`, extracts at each `n` a disjoint (Vitali) family of
cylinders `B(x_i, r_i) × (-r_i², 0)`, `r_i < δ n`, from the density hypothesis, and covers
`S ∩ B(1)` by the `5`-enlarged spatial balls `B(x_i, 5 r_i)`. The cylinders are disjoint, so the
lower bounds `ε r_i` sum to at most the (shrinking) integral over `B(1) × (-δ n, 0)`, which
`tendsto_lintegral_top_slab` sends to `0`; since each enlarged ball has `sup`-norm extended
diameter at most `10 r_i`, the Hausdorff premeasure of the cover tends to `0` as well. -/
theorem hausdorffMeasure_one_null_of_gradient_density
    (_ : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3) (S : Set Vec3) (ε : ℝ)
    (hε : 0 < ε)
    (hfin : (∫⁻ z in unitCylinder, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hdens : ∀ x ∈ S, ∀ r₀ : ℝ, 0 < r₀ → ∃ r : ℝ, 0 < r ∧ r < r₀ ∧
       ENNReal.ofReal (ε * r) ≤
         ∫⁻ z in vec3Ball x r ×ˢ Set.Ioo (-(r ^ 2)) 0, ‖Du z‖ₑ ^ (2 : ℝ)) :
    μH[1] (S ∩ vec3Ball 0 1) = 0 := by
  classical
  set F : ParabolicPoint → ℝ≥0∞ := fun z => ‖Du z‖ₑ ^ (2 : ℝ) with hFdef
  -- the shrinking scale `δ n = 1 / (n + 1)`
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hδdef
  obtain ⟨hδpos, hδle1, hδtendsto0⟩ := inverse_successor_scale_bounds
  -- the target set, as a subtype, and a chosen radius at each point and scale
  set ι : Type := ↥(S ∩ vec3Ball (0 : Vec3) 1) with hιdef
  have hsmall : ∀ z : ι, ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ r < δ n ∧
      r < 1 - vec3EuclideanNorm z.1 ∧
      ENNReal.ofReal (ε * r) ≤ ∫⁻ w in vec3Ball z.1 r ×ˢ Set.Ioo (-(r ^ 2)) 0, F w := by
    intro z n
    have hzS : z.1 ∈ S := z.2.1
    have hzB : z.1 ∈ vec3Ball (0 : Vec3) 1 := z.2.2
    have hz1 : vec3EuclideanNorm z.1 < 1 := by
      have hz1' : vec3EuclideanNorm (z.1 - 0) < 1 := hzB
      rwa [sub_zero] at hz1'
    have hmarg : (0 : ℝ) < 1 - vec3EuclideanNorm z.1 := by linarith only [hz1]
    have hr0pos : 0 < min (δ n) (1 - vec3EuclideanNorm z.1) := lt_min (hδpos n) hmarg
    obtain ⟨r, hrpos, hrlt, hbound⟩ := hdens z.1 hzS _ hr0pos
    exact ⟨r, hrpos, hrlt.trans_le (min_le_left _ _), hrlt.trans_le (min_le_right _ _), hbound⟩
  set radius : ℕ → ι → ℝ := fun n z => Classical.choose (hsmall z n) with hraddef
  have radius_spec : ∀ n z, 0 < radius n z ∧ radius n z < δ n ∧
      radius n z < 1 - vec3EuclideanNorm z.1 ∧
      ENNReal.ofReal (ε * radius n z) ≤
        ∫⁻ w in vec3Ball z.1 (radius n z) ×ˢ Set.Ioo (-(radius n z) ^ 2) 0, F w := by
    intro n z
    rw [hraddef]
    exact Classical.choose_spec (hsmall z n)
  set ball : ℕ → ι → Set ParabolicPoint :=
    fun n z => vec3Ball z.1 (radius n z) ×ˢ Set.Ioo (-(radius n z) ^ 2) (0 : ℝ) with hballdef
  have radius_le_one : ∀ n z, radius n z ≤ 1 :=
    fun n z => ((radius_spec n z).2.1.trans_le (hδle1 n)).le
  have ball_nonempty : ∀ n z, (ball n z).Nonempty := by
    intro n z
    have hr := radius_spec n z
    refine ⟨(z.1, -(radius n z) ^ 2 / 2), ?_⟩
    rw [hballdef]
    refine ⟨?_, ?_⟩
    · change vec3EuclideanNorm (z.1 - z.1) < radius n z
      rw [sub_self, vec3EuclideanNorm_zero]
      exact hr.1
    · exact ⟨by nlinarith only [hr.1], by nlinarith only [hr.1]⟩
  -- a disjoint Vitali subfamily at each scale, whose `4`-enlargements meet every candidate
  have vitali : ∀ n : ℕ, ∃ w : Set ι, w.PairwiseDisjoint (ball n) ∧
      ∀ a : ι, ∃ b ∈ w, (ball n a ∩ ball n b).Nonempty ∧ radius n a ≤ 4 * radius n b := by
    intro n
    obtain ⟨w, -, hdisj, hcover⟩ :=
      Vitali.exists_disjoint_subfamily_covering_enlargement (ball n) (Set.univ : Set ι)
        (radius n) 4 (by norm_num) (fun a _ => (radius_spec n a).1.le) 1
        (fun a _ => radius_le_one n a) (fun a _ => ball_nonempty n a)
    exact ⟨w, hdisj, fun a => hcover a (Set.mem_univ a)⟩
  set selected : ℕ → Set ι := fun n => Classical.choose (vitali n) with hseldef
  have selected_spec : ∀ n, (selected n).PairwiseDisjoint (ball n) ∧
      ∀ a : ι, ∃ b ∈ selected n, (ball n a ∩ ball n b).Nonempty ∧
        radius n a ≤ 4 * radius n b := by
    intro n; rw [hseldef]; exact Classical.choose_spec (vitali n)
  set index : ℕ → Type := fun n => {z : ι // z ∈ selected n} with hindexdef
  -- cylinders are measurable (stated directly at the `index n` level, so that later
  -- applications to `lintegral_iUnion` do not force it through an extra `.1`-composition,
  -- which elaborates very slowly against that lemma's higher-order unification problem),
  -- and lie in the unit cylinder
  have cylinder_measurable_index : ∀ n (i : index n), MeasurableSet (ball n i.1) := by
    intro n i
    rw [hballdef]
    exact (isOpen_vec3Ball i.1.1 (radius n i.1)).measurableSet.prod measurableSet_Ioo
  have cylinder_measurable : ∀ n z, MeasurableSet (ball n z) := by
    intro n z
    rw [hballdef]
    exact (isOpen_vec3Ball z.1 (radius n z)).measurableSet.prod measurableSet_Ioo
  have cylinder_subset_unitCylinder : ∀ n z, ball n z ⊆ unitCylinder := by
    intro n z
    have hr := radius_spec n z
    rw [hballdef]
    unfold unitCylinder CKN.spaceTimeSet
    refine Set.prod_mono ?_ ?_
    · exact vec3Ball_subset_unitBall_of_radius_lt_margin hr.2.2.1
    · have hsq : (radius n z) ^ 2 ≤ 1 := by
        have h1 : radius n z < δ n := hr.2.1
        have h2 : (0 : ℝ) < radius n z := hr.1
        have h3 : δ n ≤ 1 := hδle1 n
        nlinarith only [h1, h2, h3]
      exact Set.Ioo_subset_Ioo_left (by linarith only [hsq])
  -- countability of the selected family at each scale, from a finite Dirichlet-integral bound
  have hindex_countable : ∀ n, Countable (index n) := by
    intro n
    exact countable_of_positive_disjoint_integrals F (fun i : index n => ball n i.1)
      unitCylinder (fun i => ENNReal.ofReal (ε * radius n i.1))
      (fun i j hij => (selected_spec n).1 i.2 j.2 (fun h => hij (Subtype.ext h)))
      (cylinder_measurable_index n) (fun i => cylinder_subset_unitCylinder n i.1)
      (fun i => (radius_spec n i.1).2.2.2)
      (fun i => (ENNReal.ofReal_pos.mpr (mul_pos hε (radius_spec n i.1).1)).ne') hfin
  -- the enlarged spatial balls, and the containment they satisfy
  set enlarged : ∀ n, index n → Set Vec3 := fun n i => vec3Ball i.1.1 (5 * radius n i.1)
    with henldef
  have cylinder_disjoint : ∀ n {i j : index n}, i ≠ j → Disjoint (ball n i.1) (ball n j.1) :=
    fun n {i j} hij => (selected_spec n).1 i.2 j.2 (fun h => hij (Subtype.ext h))
  have enlarged_contains : ∀ n (a : ι), a.1 ∈ ⋃ i : index n, enlarged n i := by
    intro n a
    obtain ⟨b, hb, hab, hrad⟩ := (selected_spec n).2 a
    obtain ⟨w, hwa, hwb⟩ := hab
    have hfinal := mem_vec3Ball_enlargement_of_intersection a.1 b.1 w.1
      (radius n a) (radius n b) hwa.1 hwb.1 hrad
    refine mem_iUnion.2 ⟨⟨b, hb⟩, ?_⟩
    rw [henldef]
    change vec3EuclideanNorm (a.1 - b.1) < 5 * radius n b
    exact hfinal
  -- the shrinking backward slab, and the finiteness/limit of its Dirichlet integral
  set Uset : ℕ → Set ParabolicPoint :=
    fun n => vec3Ball (0 : Vec3) 1 ×ˢ Set.Ioo (-(δ n)) (0 : ℝ) with hUdef
  set I : ℕ → ℝ≥0∞ := fun n => ∫⁻ w in Uset n, F w with hIdef
  have hI_tendsto : Tendsto I atTop (nhds 0) := by
    have hwithin : Tendsto δ atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within δ hδtendsto0
        (Eventually.of_forall (fun n => hδpos n))
    have hcomp := (tendsto_lintegral_top_slab F hfin).comp hwithin
    rw [hIdef, hUdef]
    exact hcomp
  have cylinder_subset_U : ∀ n (i : index n), ball n i.1 ⊆ Uset n := by
    intro n i
    have hr := radius_spec n i.1
    rw [hballdef, hUdef]
    refine Set.prod_mono ?_ ?_
    · exact vec3Ball_subset_unitBall_of_radius_lt_margin hr.2.2.1
    · have hsq : (radius n i.1) ^ 2 ≤ δ n := by
        have h1 : radius n i.1 < δ n := hr.2.1
        have h2 : (0 : ℝ) < radius n i.1 := hr.1
        have h3 : δ n ≤ 1 := hδle1 n
        have h4 : (0 : ℝ) < δ n := hδpos n
        nlinarith only [h1, h2, h3, h4]
      exact Set.Ioo_subset_Ioo_left (by linarith only [hsq])
  have sum_integral_le : ∀ n, (∑' i : index n, ∫⁻ w in ball n i.1, F w) ≤ I n := by
    intro n
    have hInstCountable := hindex_countable n
    have heq : (∫⁻ w in ⋃ i : index n, ball n i.1, F w) =
        ∑' i : index n, ∫⁻ w in ball n i.1, F w :=
      lintegral_iUnion (cylinder_measurable_index n)
        (fun i j hij => cylinder_disjoint n hij) F
    rw [← heq, hIdef]
    exact lintegral_mono_set (Set.iUnion_subset (fun i => cylinder_subset_U n i))
  -- the enlarged-ball diameters, in terms of the density lower bound
  set K : ℝ≥0∞ := ENNReal.ofReal (10 / ε) with hKdef
  have hKe : K * ENNReal.ofReal ε = ENNReal.ofReal 10 := by
    rw [hKdef, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 10 / ε)]
    congr 1
    field_simp
  have diameter_integral_le : ∀ n (i : index n),
      Metric.ediam (enlarged n i) ≤ K * (∫⁻ w in ball n i.1, F w) := by
    intro n i
    have hstep : ENNReal.ofReal (10 * radius n i.1) = K * ENNReal.ofReal (ε * radius n i.1) := by
      rw [ENNReal.ofReal_mul hε.le, ← mul_assoc, hKe,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)]
    calc Metric.ediam (enlarged n i) ≤ ENNReal.ofReal (2 * (5 * radius n i.1)) := by
          rw [henldef]; exact ediam_vec3Ball_le i.1.1 (5 * radius n i.1)
      _ = ENNReal.ofReal (10 * radius n i.1) := by rw [show 2 * (5 * radius n i.1) =
            10 * radius n i.1 by ring]
      _ = K * ENNReal.ofReal (ε * radius n i.1) := hstep
      _ ≤ K * (∫⁻ w in ball n i.1, F w) :=
          mul_le_mul_of_nonneg_left (radius_spec n i.1).2.2.2 bot_le
  have diameter_sum_le : ∀ n, (∑' i : index n, Metric.ediam (enlarged n i) ^ (1 : ℝ)) ≤ K * I n
    := by
    intro n
    calc (∑' i : index n, Metric.ediam (enlarged n i) ^ (1 : ℝ))
        = ∑' i : index n, Metric.ediam (enlarged n i) := by simp only [ENNReal.rpow_one]
      _ ≤ ∑' i : index n, K * (∫⁻ w in ball n i.1, F w) :=
          ENNReal.tsum_le_tsum (fun i => diameter_integral_le n i)
      _ = K * ∑' i : index n, ∫⁻ w in ball n i.1, F w := ENNReal.tsum_mul_left
      _ ≤ K * I n := mul_le_mul_of_nonneg_left (sum_integral_le n) bot_le
  -- the covering radius bound tends to `0`
  have hr_tendsto : Tendsto (fun n : ℕ => (10 : ℝ≥0∞) * ENNReal.ofReal (δ n)) atTop (nhds 0) := by
    have hofReal : Tendsto (fun n => ENNReal.ofReal (δ n)) atTop (nhds 0) := by
      have h := ENNReal.tendsto_ofReal hδtendsto0
      simpa only [hδdef, ENNReal.ofReal_zero] using h
    have h := ENNReal.Tendsto.const_mul (a := (10 : ℝ≥0∞)) hofReal (Or.inr (by norm_num))
    simpa using h
  have hcover_eventually : ∀ n, S ∩ vec3Ball (0 : Vec3) 1 ⊆ ⋃ i : index n, enlarged n i := by
    intro n x hx
    exact enlarged_contains n ⟨x, hx⟩
  have hdiam_eventually : ∀ n, ∀ i : index n,
      Metric.ediam (enlarged n i) ≤ (10 : ℝ≥0∞) * ENNReal.ofReal (δ n) := by
    intro n i
    calc Metric.ediam (enlarged n i) ≤ ENNReal.ofReal (2 * (5 * radius n i.1)) := by
          rw [henldef]; exact ediam_vec3Ball_le i.1.1 (5 * radius n i.1)
      _ = (10 : ℝ≥0∞) * ENNReal.ofReal (radius n i.1) := by
          rw [show 2 * (5 * radius n i.1) = 10 * radius n i.1 by ring,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)]
          norm_num
      _ ≤ (10 : ℝ≥0∞) * ENNReal.ofReal (δ n) :=
          mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (radius_spec n i.1).2.1.le) bot_le
  have hausdorff_le_liminf :
      μH[(1 : ℝ)] (S ∩ vec3Ball (0 : Vec3) 1) ≤
        liminf (fun n => ∑' i : index n, Metric.ediam (enlarged n i) ^ (1 : ℝ)) atTop := by
    have hInstCountable := hindex_countable
    exact MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum (1 : ℝ)
      (S ∩ vec3Ball (0 : Vec3) 1) (fun n : ℕ => (10 : ℝ≥0∞) * ENNReal.ofReal (δ n)) hr_tendsto
      (fun n i => enlarged n i) (Eventually.of_forall hdiam_eventually)
      (Eventually.of_forall hcover_eventually)
  have hsum_tendsto0 :
      Tendsto (fun n => ∑' i : index n, Metric.ediam (enlarged n i) ^ (1 : ℝ)) atTop (nhds 0) := by
    have hupper : Tendsto (fun n => K * I n) atTop (nhds 0) := by
      have hKne : K ≠ ⊤ := by rw [hKdef]; exact ENNReal.ofReal_ne_top
      have h := ENNReal.Tendsto.const_mul (a := K) hI_tendsto (Or.inr hKne)
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall (fun n => bot_le)) (Eventually.of_forall diameter_sum_le)
  have hliminf0 :
      liminf (fun n => ∑' i : index n, Metric.ediam (enlarged n i) ^ (1 : ℝ)) atTop = 0 :=
    hsum_tendsto0.liminf_eq
  have hle0 : μH[(1 : ℝ)] (S ∩ vec3Ball (0 : Vec3) 1) ≤ 0 := by
    rw [← hliminf0]; exact hausdorff_le_liminf
  exact le_antisymm hle0 bot_le

/-! ### From a strict limsup lower density to the covering lemma's density hypothesis -/

/-- **The bridge from a strict-limsup gradient density to
`hausdorffMeasure_one_null_of_gradient_density`'s
`hdens` hypothesis.** If `ofReal ε₁` is at most the `limsup`, as the radius shrinks to `0` from
the right, of `(ofReal r)⁻¹` times the Dirichlet integral of `spatialGradientSq u Du` over the
backward parabolic cylinder `B(x,r) × (-r², 0)`, then at every scale `r₀ > 0` there is a smaller
radius `r < r₀` with `ofReal (ε₁/18 * r) ≤ ∫ ‖Du‖ₑ²` over that same cylinder — exactly the form
`hausdorffMeasure_one_null_of_gradient_density` consumes, at `ε := ε₁ / 18`. The constant loses a
factor of `2` because a strict `limsup` bound only gives, at every neighbourhood of `0`, a point
where the halved level `ε₁/2` is exceeded (not `ε₁` itself), and a further factor of `9` bridging
`spatialGradientSq` to the `enorm`-squared integrand of
`hausdorffMeasure_one_null_of_gradient_density`
(`ofReal_spatialGradientSq_le_nine`), so only `ε₁/(2·9) = ε₁/18` survives. -/
theorem density_of_le_limsup {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {x : Vec3} {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (h : ENNReal.ofReal ε₁ ≤ Filter.limsup (fun r : ℝ => (ENNReal.ofReal r)⁻¹ *
        ∫⁻ w in vec3Ball x r ×ˢ Set.Ioo (-(r ^ 2)) 0,
          ENNReal.ofReal (spatialGradientSq u Du w)) (𝓝[>] (0 : ℝ)))
    (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ r : ℝ, 0 < r ∧ r < r₀ ∧ ENNReal.ofReal (ε₁ / 18 * r) ≤
      ∫⁻ w in vec3Ball x r ×ˢ Set.Ioo (-(r ^ 2)) 0, ‖Du w‖ₑ ^ (2 : ℝ) := by
  set f : ℝ → ℝ≥0∞ := fun r : ℝ => (ENNReal.ofReal r)⁻¹ *
      ∫⁻ w in vec3Ball x r ×ˢ Set.Ioo (-(r ^ 2)) 0, ENNReal.ofReal (spatialGradientSq u Du w)
    with hfdef
  have hlt : ENNReal.ofReal (ε₁ / 2) < ENNReal.ofReal ε₁ := by
    refine ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr ?_
    linarith only [hε₁]
  have hlt2 : ENNReal.ofReal (ε₁ / 2) < Filter.limsup f (𝓝[>] (0 : ℝ)) := lt_of_lt_of_le hlt h
  have hmem : Set.Ioo (0 : ℝ) r₀ ∈ 𝓝[>] (0 : ℝ) := by
    have h1 : Set.Iio r₀ ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hr₀
    have h2 := inter_mem_nhdsWithin (Set.Ioi (0 : ℝ)) h1
    rwa [Ioi_inter_Iio] at h2
  rw [Filter.limsup_eq_iInf_iSup] at hlt2
  have hle : (⨅ s ∈ 𝓝[>] (0 : ℝ), ⨆ a ∈ s, f a) ≤ ⨆ a ∈ Set.Ioo (0 : ℝ) r₀, f a :=
    iInf₂_le (Set.Ioo (0 : ℝ) r₀) hmem
  have hlt3 : ENNReal.ofReal (ε₁ / 2) < ⨆ a ∈ Set.Ioo (0 : ℝ) r₀, f a := lt_of_lt_of_le hlt2 hle
  rw [lt_iSup_iff] at hlt3
  obtain ⟨r, hlt4⟩ := hlt3
  rw [lt_iSup_iff] at hlt4
  obtain ⟨hrmem, hlt5⟩ := hlt4
  obtain ⟨hr0, hrr0⟩ := hrmem
  refine ⟨r, hr0, hrr0, ?_⟩
  rw [hfdef] at hlt5
  simp only at hlt5
  have hrne0 : (ENNReal.ofReal r) ≠ 0 := (ENNReal.ofReal_pos.mpr hr0).ne'
  have hrnetop : (ENNReal.ofReal r) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdiv : ENNReal.ofReal (ε₁ / 2) <
      (∫⁻ w in vec3Ball x r ×ˢ Set.Ioo (-(r ^ 2)) 0,
          ENNReal.ofReal (spatialGradientSq u Du w)) / (ENNReal.ofReal r) := by
    have hswap : (∫⁻ w in vec3Ball x r ×ˢ Set.Ioo (-(r ^ 2)) 0,
        ENNReal.ofReal (spatialGradientSq u Du w)) / (ENNReal.ofReal r)
        = (ENNReal.ofReal r)⁻¹ * ∫⁻ w in vec3Ball x r ×ˢ Set.Ioo (-(r ^ 2)) 0,
            ENNReal.ofReal (spatialGradientSq u Du w) := by
      rw [div_eq_mul_inv, mul_comm]
    rw [hswap]
    exact hlt5
  have hmullt := (ENNReal.lt_div_iff_mul_lt (Or.inl hrne0) (Or.inl hrnetop)).mp hdiv
  have hmuleq : ENNReal.ofReal (ε₁ / 2) * ENNReal.ofReal r = ENNReal.ofReal (ε₁ / 2 * r) :=
    (ENNReal.ofReal_mul (by positivity)).symm
  rw [hmuleq] at hmullt
  -- bridge the integrand: `spatialGradientSq ≤ 9 ‖Du‖ₑ²`
  have hbridge : (∫⁻ w in vec3Ball x r ×ˢ Set.Ioo (-(r ^ 2)) 0,
      ENNReal.ofReal (spatialGradientSq u Du w))
      ≤ 9 * ∫⁻ w in vec3Ball x r ×ˢ Set.Ioo (-(r ^ 2)) 0, ‖Du w‖ₑ ^ (2 : ℝ) := by
    calc (∫⁻ w in vec3Ball x r ×ˢ Set.Ioo (-(r ^ 2)) 0,
        ENNReal.ofReal (spatialGradientSq u Du w))
        ≤ ∫⁻ w in vec3Ball x r ×ˢ Set.Ioo (-(r ^ 2)) 0, 9 * ‖Du w‖ₑ ^ (2 : ℝ) :=
          lintegral_mono (fun w => ofReal_spatialGradientSq_le_nine u Du w)
      _ = 9 * ∫⁻ w in vec3Ball x r ×ˢ Set.Ioo (-(r ^ 2)) 0, ‖Du w‖ₑ ^ (2 : ℝ) :=
          lintegral_const_mul' 9 _ (by norm_num)
  have hfinal9 : ENNReal.ofReal (ε₁ / 2 * r) <
      9 * ∫⁻ w in vec3Ball x r ×ˢ Set.Ioo (-(r ^ 2)) 0, ‖Du w‖ₑ ^ (2 : ℝ) :=
    lt_of_lt_of_le hmullt hbridge
  -- clear the factor `9`
  have h9eq : ENNReal.ofReal (ε₁ / 2 * r) = 9 * ENNReal.ofReal (ε₁ / 18 * r) := by
    have : ε₁ / 2 * r = 9 * (ε₁ / 18 * r) := by ring
    rw [this, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 9)]
    norm_num
  rw [h9eq] at hfinal9
  have h9ne0 : (9 : ℝ≥0∞) ≠ 0 := by norm_num
  have h9netop : (9 : ℝ≥0∞) ≠ ⊤ := by norm_num
  exact le_of_lt ((ENNReal.mul_right_strictMono h9ne0 h9netop).lt_iff_lt.mp hfinal9)

end CIV
