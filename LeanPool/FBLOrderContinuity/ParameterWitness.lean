/-
Copyright (c) 2026 Raúl E. Pariente-Martín, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raúl E. Pariente-Martín, Pedro Tradacete
-/

module

public import LeanPool.FBLOrderContinuity.Extension



/-!
# Compact witnesses for a change of convexity parameter

This module supplies Proposition 5.2 and the obstruction used in Theorem 5.1.
A nonsurjective inclusion from `Free p E` to `Free q E` separates the two norms on
the common algebraic core. Compact support majorants and a summable Minkowski sum
turn this separation into a compact disk whose support belongs to the target but
has infinite source free norm.

`compact_support_finite_approximation` approximates that support by increasing
finite suprema of evaluations. `parameter_failure_witness` then produces a positive
algebraic sequence decreasing to zero in the source whose images converge in norm
to a strictly positive target element. All constructions allow q = infinity.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal Topology
open Filter Set
universe u
namespace FBLOrderContinuousLH

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The parameter inclusion agrees with the common algebraic free-lattice model. -/
theorem inclusion_ofFVL {p q : Exponent} (hpq : p ≤ q) (v : FVL E) :
    inclusion hpq (ofFVL p v) = ofFVL q v := by
  apply Subtype.ext
  apply Subtype.ext
  funext φ
  exact inclusion_apply hpq _ φ

/-- If the canonical parameter inclusion is not surjective, then for any a, b > 0
there is an algebraic element of p-free norm exactly a and q-free norm less than b.
Otherwise a lower bound on the dense algebraic core would make the dense inclusion
have closed range, forcing surjectivity. -/
theorem parameter_norm_separation {p q : Exponent} (hpq : p ≤ q)
    (honto : ¬ Function.Surjective (inclusion (E := E) hpq))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ v : FVL E, ‖ofFVL p v‖ = a ∧ ‖ofFVL q v‖ < b := by
  have hnot : ¬ BoundedBelow (inclusion (E := E) hpq) := by
    intro h
    have hc := ((embedding_iff (inclusion (E := E) hpq).toContinuousLinearMap).mp h).2
    apply honto
    rw [← Set.range_eq_univ, ← hc.closure_eq]
    exact (inclusion_properties (E := E) hpq).2.2.1.closure_range
  have hbad : ∃ v : FVL E, ‖ofFVL q v‖ < (b / a) * ‖ofFVL p v‖ := by
    by_contra! h
    apply hnot
    refine ⟨b / a, div_pos hb ha, fun f => ?_⟩
    exact (denseRange_ofFVL p).induction_on f
      (isClosed_le (continuous_const.mul continuous_norm)
        (inclusion hpq).toContinuousLinearMap.continuous.norm)
      (fun v => by simpa only [inclusion_ofFVL] using h v)
  obtain ⟨v, hv⟩ := hbad
  have hvpos : 0 < ‖ofFVL p v‖ :=
    (mul_pos_iff_of_pos_left (div_pos hb ha)).mp ((norm_nonneg _).trans_lt hv)
  refine ⟨(a / ‖ofFVL p v‖) • v, ?_, ?_⟩
  · rw [map_smul, norm_smul, Real.norm_of_nonneg (div_pos ha hvpos).le]
    exact div_mul_cancel₀ a hvpos.ne'
  · rw [map_smul, norm_smul, Real.norm_of_nonneg (div_pos ha hvpos).le]
    calc
      _ < (a / ‖ofFVL p v‖) * ((b / a) * ‖ofFVL p v‖) :=
        mul_lt_mul_of_pos_left hv (div_pos ha hvpos)
      _ = b := by field_simp

/-- The support of the unit ball in a finite-dimensional space is the dual norm. -/
theorem support_unitBall [FiniteDimensional ℝ E] (φ : Dual E) :
    support (Metric.closedBall (0 : E) 1) φ = ‖φ‖ := by
  have hne : (Metric.closedBall (0 : E) 1).Nonempty := ⟨0, by simp⟩
  have hb := (isCompact_closedBall (0 : E) 1).isBounded
  have hsupport : BddAbove ((fun x : E => |φ x|) '' Metric.closedBall 0 1) := by
    refine ⟨‖φ‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (φ.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg φ)
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx))
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro _ ⟨x, hx, rfl⟩
    exact (φ.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg φ)
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx))
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm
      (apply_nonneg (supportSeminorm _ hne hb) φ)
    intro x hx
    exact le_csSup hsupport ⟨x, by simp [Metric.mem_closedBall, dist_zero_right, hx], rfl⟩

/-- For finite q, the majorant-norm formula gives a compact absolutely convex support
majorant of an algebraic element with any prescribed positive norm error. -/
private theorem finite_parameter_compact_majorant [CompleteSpace E]
    (q : Exponent) (hq : q.IsFinite) (v : FVL E) (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : Set E) (h : Free q E), K.Nonempty ∧ AbsConvex ℝ K ∧ IsCompact K ∧
      (∀ φ, h φ = support K φ) ∧
      (∀ φ, |fvlFunction v φ| ≤ h φ) ∧ ‖h‖ < ‖ofFVL q v‖ + ε := by
  obtain ⟨r, ⟨n, x, rfl, hmajor⟩, hcost⟩ := exists_lt_of_csInf_lt
    (fvl_majorant_nonempty q hq v)
    (by rw [← majorant_norm q hq]; exact lt_add_of_pos_right _ hε)
  obtain ⟨K, hK, _, hs⟩ := finite_family_disk_in_span q hq x
  obtain ⟨hne, hac, hc⟩ := summable_disk_compact q K hK
  refine ⟨K, latticePSum q (fun i => delta q (x i)), hne, hac, hc, ?_, ?_, ?_⟩
  · intro φ
    exact (latticePSum_apply q q _ φ).trans (hs φ).symm
  · intro φ
    rw [latticePSum_apply]
    exact hmajor φ
  · exact ((free_pConvex (E := E) q).2 n (fun i => delta q (x i))).trans_lt
      (by simpa only [one_mul, (delta q).norm_map] using hcost)

/-- At the infinity endpoint, an algebraic element has a compact support majorant
whose free norm is no larger than its own. Work in the finite-dimensional span of
its generators and map a scaled unit ball into the original space. -/
private theorem infinity_compact_majorant [CompleteSpace E] (v : FVL E) :
    ∃ (K : Set E) (h : Free Exponent.infinity E),
      K.Nonempty ∧ AbsConvex ℝ K ∧ IsCompact K ∧
      (∀ φ, h φ = support K φ) ∧
      (∀ φ, |fvlFunction v φ| ≤ h φ) ∧ ‖h‖ ≤ ‖ofFVL Exponent.infinity v‖ := by
  obtain ⟨A, hA, hgen⟩ := fvl_finite_generators Exponent.infinity v
  let M := Submodule.span ℝ A
  let : FiniteDimensional ℝ M := FiniteDimensional.span_of_finite (K := ℝ) hA
  obtain ⟨w, hw⟩ := hgen M Submodule.subset_span
  have hi := (poe_one_iff_isometry Exponent.infinity M M.closed_of_finiteDimensional).mp
    (poe_infinity_one M M.closed_of_finiteDimensional)
  have hwNorm : ‖w‖ = ‖ofFVL Exponent.infinity v‖ :=
    (hi.norm_map_of_map_zero (map_zero (induced Exponent.infinity M.subtypeL).toContinuousLinearMap)
      w).symm.trans (congrArg norm hw)
  let c := ‖ofFVL Exponent.infinity v‖
  let L : M →L[ℝ] E := c • M.subtypeL
  let K : Set E := L '' Metric.closedBall 0 1
  have hball : IsPCompactDisk Exponent.infinity (Metric.closedBall (0 : M) 1) :=
    (isPCompactDisk_infinity_iff _).mpr ⟨⟨0, by simp⟩,
      ⟨balanced_closedBall_zero, convex_closedBall _ _⟩, isCompact_closedBall _ _⟩
  have hK := pCompactDisk_image Exponent.infinity _ hball L
  obtain ⟨hne, hac, hc⟩ := summable_disk_compact Exponent.infinity K hK
  obtain ⟨h, hh⟩ := compact_support_inFree_infinity K hc
  have hs (φ : Dual E) : support K φ = c * ‖φ.comp M.subtypeL‖ := by
    change support (L '' Metric.closedBall 0 1) φ = _
    simp only [support, compactSupport, Set.image_image]
    change support (Metric.closedBall 0 1) (φ.comp L) = _
    rw [support_unitBall, show φ.comp L = c • φ.comp M.subtypeL from
      ContinuousLinearMap.comp_smul φ c M.subtypeL, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
  refine ⟨K, h, hne, hac, hc, hh, ?_, ?_⟩
  · intro φ
    rw [hh, hs]
    have heq : fvlFunction v φ = w (φ.comp M.subtypeL) := by
      rw [← (model_evaluation Exponent.infinity (0 : E) v φ).2, ← hw, canonical_map_formulas]
    rw [heq, mul_comm c]
    exact (hp_apply_abs_le Exponent.infinity w.1 _).trans_eq
      (congrArg (‖φ.comp M.subtypeL‖ * ·) hwNorm)
  · apply (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).mp
    rw [← freeNormExt_eq_norm]
    change (⨆ φ, ⨆ (_ : ‖φ‖ ≤ 1), ENNReal.ofReal |h φ|) ≤ _
    refine iSup_le fun φ => iSup_le fun hφ => ENNReal.ofReal_le_ofReal ?_
    rw [hh, hs, abs_of_nonneg
      (mul_nonneg (show 0 ≤ c from norm_nonneg _) (norm_nonneg (φ.comp M.subtypeL)))]
    have hrestrict : ‖φ.comp M.subtypeL‖ ≤ 1 := by
      apply (φ.comp M.subtypeL).opNorm_le_bound zero_le_one
      intro x
      exact (φ.le_opNorm (x : E)).trans
        (mul_le_mul_of_nonneg_right hφ (norm_nonneg x))
    exact mul_le_of_le_one_right (norm_nonneg _) hrestrict

/-- Every algebraic free function has a nonempty absolutely convex compact support
majorant whose q-free norm is within ε of its own, for any ε > 0. Finite q uses
finite p-sum majorants; q = ∞ uses the finite-dimensional span of the generators.
The majorant dominates the absolute value on the whole continuous dual. -/
theorem parameter_compact_majorant [CompleteSpace E]
    (q : Exponent) (v : FVL E) (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : Set E) (h : Free q E), K.Nonempty ∧ AbsConvex ℝ K ∧ IsCompact K ∧
      (∀ φ, h φ = support K φ) ∧
      (∀ φ, |fvlFunction v φ| ≤ h φ) ∧ ‖h‖ < ‖ofFVL q v‖ + ε := by
  rcases lt_or_eq_of_le (le_top : q.1 ≤ ⊤) with hq | hq
  · exact finite_parameter_compact_majorant q hq v ε hε
  · have heq : q = Exponent.infinity := Subtype.ext hq
    subst q
    obtain ⟨K, h, hne, hac, hc, hh, hdom, hnorm⟩ := infinity_compact_majorant v
    exact ⟨K, h, hne, hac, hc, hh, hdom, hnorm.trans_lt (lt_add_of_pos_right _ hε)⟩

/-- Evaluation at a fixed dual functional as a continuous linear functional on
`Free p E`. The estimate `hp_apply_abs_le` bounds its operator norm by the norm
of the dual functional and allows evaluation to commute with norm-convergent series. -/
def freeEvalCLM (p : Exponent) (φ : Dual E) : Free p E →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => f φ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ‖φ‖ (fun f => hp_apply_abs_le p f.1 φ)

private theorem norm_le_of_support_representation (p : Exponent) (K : Set E)
    (hK : IsCompact K) (h : Free p E) (hh : ∀ φ, h φ = support K φ)
    {x : E} (hx : x ∈ K) : ‖x‖ ≤ ‖h‖ := by
  obtain ⟨φ, hφ, hφx⟩ := exists_dual_vector'' ℝ x
  have hb : BddAbove ((fun y : E => |φ y|) '' K) :=
    (hK.image φ.continuous.abs).bddAbove
  calc
    ‖x‖ = |φ x| := by simpa using (congrArg abs hφx).symm
    _ ≤ support K φ := le_csSup hb (Set.mem_image_of_mem _ hx)
    _ ≤ |h φ| := by rw [← hh]; exact le_abs_self _
    _ ≤ ‖φ‖ * ‖h‖ := hp_apply_abs_le p h.1 φ
    _ ≤ ‖h‖ := mul_le_of_le_one_left (norm_nonneg _) hφ

/-- Nonsurjectivity of the parameter inclusion yields a nonempty absolutely convex
compact set whose support belongs to `Free q E` with norm at most one but has
infinite p-free norm. A summable series of compact majorants turns arbitrarily
large algebraic norm separation into this single support-function witness. -/
theorem parameter_support_separation [CompleteSpace E] {p q : Exponent} (hpq : p ≤ q)
    (honto : ¬ Function.Surjective (inclusion (E := E) hpq)) :
    ∃ K : Set E, K.Nonempty ∧ AbsConvex ℝ K ∧ IsCompact K ∧
      ∃ r : Free q E, (∀ φ, r φ = support K φ) ∧
        0 ≤ r ∧ ‖r‖ ≤ 1 ∧ freeNormExt p (support K) = ⊤ := by
  choose v hv hsmall using fun n : ℕ =>
    parameter_norm_separation hpq honto (n + 1) ((1 / 2 : ℝ) ^ n / 4)
      (by positivity) (by positivity)
  choose K r hne hac hc hr hdom hnorm using fun n =>
    parameter_compact_majorant q (v n) ((1 / 2 : ℝ) ^ n / 4) (by positivity)
  have hnorm' (n : ℕ) : ‖r n‖ ≤ (1 / 2 : ℝ) ^ n / 2 := by
    have hn := hnorm n
    have hs := hsmall n
    linarith
  have hsum : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n / 2) :=
    summable_geometric_two.div_const 2
  have hrnorm : Summable (fun n => ‖r n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm' hsum
  have hrsum : Summable r := hrnorm.of_norm
  have hbound (n : ℕ) (x : E) (hx : x ∈ K n) : ‖x‖ ≤ (1 / 2 : ℝ) ^ n / 2 :=
    (norm_le_of_support_representation q (K n) (hc n) (r n) (hr n) hx).trans (hnorm' n)
  obtain ⟨hDne, hDac, hDc, hDs⟩ := seriesDisk_properties K
    (fun n => (1 / 2 : ℝ) ^ n / 2) (fun _ => by positivity) hsum
    (fun n => ⟨hne n, hac n, hc n⟩) hbound
  have hrpos (n : ℕ) : 0 ≤ r n := by
    intro φ
    rw [hr]
    exact apply_nonneg (supportSeminorm _ (hne n) (hc n).isBounded) φ
  have hrep (φ : Dual E) : (∑' n, r n) φ = support (seriesDisk K) φ := by
    rw [hDs]
    exact ((freeEvalCLM q φ).map_tsum hrsum).trans
      (tsum_congr fun n => hr n φ)
  refine ⟨seriesDisk K, hDne, hDac, hDc, ∑' n, r n, hrep, tsum_nonneg hrpos, ?_, ?_⟩
  · calc
      ‖∑' n, r n‖ ≤ ∑' n, ‖r n‖ := norm_tsum_le_tsum_norm hrnorm
      _ ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ n / 2 := hrnorm.tsum_le_tsum hnorm' hsum
      _ = 1 := by rw [tsum_div_const, tsum_geometric_two]; norm_num
  · by_contra hfin
    obtain ⟨n, hn⟩ := exists_nat_gt (freeNormExt p (support (seriesDisk K))).toReal
    have hnorm : freeNormExt p (ofFVL p (v n)) ≤ freeNormExt p (support (seriesDisk K)) := by
      apply freeNormExt_mono_abs
      intro φ
      rw [(model_evaluation p (0 : E) _ _).2, ← hrep]
      exact (hdom n φ).trans
        (((hrsum.le_tsum n (fun k _ => hrpos k)) φ).trans (le_abs_self _))
    rw [freeNormExt_eq_norm] at hnorm
    have hh := ENNReal.toReal_mono hfin hnorm
    rw [ENNReal.toReal_ofReal (norm_nonneg _), hv] at hh
    linarith

/-- Closed absolutely convex sets are determined by their support bounds. -/
theorem mem_of_abs_eval_le_support (K : Set E) (hne : K.Nonempty)
    (hac : AbsConvex ℝ K) (hc : IsClosed K) (x : E)
    (hx : ∀ φ : Dual E, |φ x| ≤ support K φ) : x ∈ K := by
  by_contra hnot
  obtain ⟨φ, a, hφ, hax⟩ := geometric_hahn_banach_closed_point hac.2 hc hnot
  have hs : support K φ ≤ a := by
    apply csSup_le (hne.image _)
    rintro _ ⟨y, hy, rfl⟩
    apply abs_le.mpr
    refine ⟨?_, (hφ y hy).le⟩
    have hneg : -y ∈ K := by
      simpa only [neg_one_smul] using hac.1.smul_mem (a := (-1 : ℝ)) (by norm_num) hy
    have hh := hφ (-y) hneg
    rw [map_neg] at hh
    linarith
  exact hax.not_ge ((le_abs_self _).trans ((hx φ).trans hs))

private theorem support_mono_compact {A K : Set E} (hA : A.Nonempty) (hK : IsCompact K)
    (hAK : A ⊆ K) (φ : Dual E) : support A φ ≤ support K φ := by
  apply csSup_le (hA.image _)
  rintro _ ⟨x, hx, rfl⟩
  exact le_csSup (hK.image φ.continuous.abs).bddAbove (Set.mem_image_of_mem _ (hAK hx))

private theorem finiteSupport_nonnegative (A : Finset E) : 0 ≤ finiteSupport A := by
  classical
  by_cases hA : A.Nonempty
  · exact (abs_nonneg (FVLv.of hA.choose)).trans (by
      simpa only [finiteSupport, dite_eq_left hA] using
        Finset.le_sup' (fun a : E => |FVLv.of a|) hA.choose_spec)
  · simp [finiteSupport, hA]

private theorem finiteSupport_mono {A B : Finset E} (hAB : A ⊆ B) :
    finiteSupport A ≤ finiteSupport B := by
  classical
  by_cases hA : A.Nonempty
  · rw [finiteSupport, dite_eq_left hA, finiteSupport, dite_eq_left (hA.mono hAB)]
    exact Finset.sup'_le _ _ (fun a ha => Finset.le_sup' (fun b : E => |FVLv.of b|) (hAB ha))
  · simpa only [finiteSupport, dite_eq_right hA] using finiteSupport_nonnegative B

omit [NormedSpace ℝ E] in
private theorem compact_finite_net (K : Set E) (hne : K.Nonempty) (hc : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Finset E, A.Nonempty ∧ (A : Set E) ⊆ K ∧
      ∀ x ∈ K, ∃ y ∈ A, dist x y < ε := by
  classical
  obtain ⟨A, hAK, hAf, hcover⟩ := hc.elim_finite_subcover_image
    (b := K) (c := fun y => Metric.ball y ε) (fun _ _ => Metric.isOpen_ball)
    (by intro x hx; exact Set.mem_iUnion₂.mpr ⟨x, hx, Metric.mem_ball_self hε⟩)
  have hnet (x : E) (hx : x ∈ K) : ∃ y ∈ hAf.toFinset, dist x y < ε := by
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
    exact ⟨y, hAf.mem_toFinset.mpr hy, hxy⟩
  obtain ⟨y, hy, _⟩ := hnet hne.some hne.some_mem
  exact ⟨hAf.toFinset, ⟨y, hy⟩, fun x hx => hAK (hAf.mem_toFinset.mp hx), hnet⟩

private theorem finite_net_support_norm (K : Set E) (hne : K.Nonempty) (hc : IsCompact K)
    (r : Free Exponent.infinity E) (hr : ∀ φ, r φ = support K φ)
    (A : Finset E) (hA : A.Nonempty) (hAK : (A : Set E) ⊆ K)
    (ε : ℝ) (hε : 0 < ε) (hnet : ∀ x ∈ K, ∃ y ∈ A, dist x y < ε) :
    ‖r - ofFVL Exponent.infinity (finiteSupport A)‖ ≤ ε := by
  apply (ENNReal.ofReal_le_ofReal_iff hε.le).mp
  rw [← freeNormExt_eq_norm]
  change (⨆ φ, ⨆ (_ : ‖φ‖ ≤ 1),
    ENNReal.ofReal |r φ - fvlFunction (finiteSupport A) φ|) ≤ ENNReal.ofReal ε
  refine iSup_le fun φ => iSup_le fun hφ => ENNReal.ofReal_le_ofReal ?_
  rw [hr, finiteSupport_support A hA, abs_of_nonneg
    (sub_nonneg.mpr (support_mono_compact hA.to_set hc hAK φ))]
  apply sub_le_iff_le_add.mpr
  apply csSup_le (hne.image _)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hnet x hx
  have hybound : |φ y| ≤ support (A : Set E) φ :=
    le_csSup ((A.finite_toSet.isCompact.image φ.continuous.abs).bddAbove)
      (Set.mem_image_of_mem _ hy)
  have hdiff : |φ (x - y)| ≤ ε := by
    exact (φ.le_opNorm (x - y)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hφ).trans (by
        simpa only [dist_eq_norm] using hxy.le))
  calc
    |φ x| ≤ |φ (x - y)| + |φ y| := by
      simpa only [map_sub, sub_add_cancel] using abs_add_le (φ (x - y)) (φ y)
    _ ≤ ε + support (A : Set E) φ := add_le_add hdiff hybound

/-- If the support of a nonempty compact K is represented in `Free q E`, it is
the norm limit of finite-support functions from increasing nonempty finite subsets
of K. Finite q follows from summable-disk approximation; the endpoint follows
from finite nets in K. These nested approximants supply the algebraic failure witness. -/
theorem compact_support_finite_approximation [CompleteSpace E]
    (q : Exponent) (K : Set E) (hne : K.Nonempty) (hc : IsCompact K)
    (r : Free q E) (hr : ∀ φ, r φ = support K φ) :
    ∃ B : ℕ → Finset E, Monotone B ∧
      (∀ n, (B n).Nonempty ∧ (B n : Set E) ⊆ K) ∧
      Tendsto (fun n => ofFVL q (finiteSupport (B n))) atTop (𝓝 r) := by
  classical
  rcases lt_or_eq_of_le (le_top : q.1 ≤ ⊤) with hq | hq
  · obtain ⟨L, hL, hdom⟩ := summable_global_domination q r
    obtain ⟨hLne, hLa, hLc⟩ := summable_disk_compact q L hL
    have hKL : K ⊆ L := by
      intro x hx
      apply mem_of_abs_eval_le_support L hLne hLa hLc.isClosed x
      intro φ
      have hx' : |φ x| ≤ support K φ :=
        le_csSup (hc.image φ.continuous.abs).bddAbove (Set.mem_image_of_mem _ hx)
      calc
        |φ x| ≤ support K φ := hx'
        _ = r φ := (hr φ).symm
        _ ≤ |r φ| := le_abs_self _
        _ ≤ support L φ := hdom φ
    obtain ⟨s, hs, _, B, hBm, hB, _, hlim⟩ := subsets_summable_disk q hq K L hne hKL hL
    have hsr : s = r := by
      apply Subtype.ext
      apply Subtype.ext
      funext φ
      exact (hs φ).trans (hr φ).symm
    exact ⟨B, hBm, hB, hsr ▸ hlim⟩
  · have heq : q = Exponent.infinity := Subtype.ext hq
    subst q
    choose A hA hAK hnet using fun n : ℕ =>
      compact_finite_net K hne hc ((1 / 2 : ℝ) ^ n) (by positivity)
    let B (n : ℕ) : Finset E := (Finset.range (n + 1)).biUnion A
    have hAB (n : ℕ) : A n ⊆ B n :=
      Finset.subset_biUnion_of_mem A (Finset.mem_range.mpr (Nat.lt_succ_self n))
    have hBm : Monotone B := fun n m hnm =>
      Finset.biUnion_subset_biUnion_of_subset_left A
        (Finset.range_mono (Nat.add_le_add_right hnm 1))
    have hBn (n : ℕ) : (B n).Nonempty := (hA n).mono (hAB n)
    have hBK (n : ℕ) : (B n : Set E) ⊆ K := by
      intro x hx
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
      exact hAK i hi
    refine ⟨B, hBm, fun n => ⟨hBn n, hBK n⟩, ?_⟩
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => ?_) summable_geometric_two.tendsto_atTop_zero
    rw [norm_sub_rev]
    apply finite_net_support_norm K hne hc r hr (B n) (hBn n) (hBK n) _ (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet n x hx
    exact ⟨y, hAB n hy, hxy⟩

/-- A compact support with q-free norm at most one and infinite p-free norm gives
a positive algebraic sequence decreasing to zero in the p-free lattice. Its images
in the q-free lattice converge in norm to a strictly positive element that is
below every image. This realizes `FVLFailureWitness` for the canonical inclusion. -/
theorem parameter_failure_witness [CompleteSpace E] {p q : Exponent} (hpq : p < q)
    (K : Set E) (hne : K.Nonempty) (hac : AbsConvex ℝ K) (hc : IsCompact K)
    (r : Free q E) (hr : ∀ φ, r φ = support K φ) (hrnorm : ‖r‖ ≤ 1)
    (hinf : freeNormExt p (support K) = ⊤) :
    FVLFailureWitness p q (inclusion (E := E) hpq.le) := by
  classical
  have hp : p.IsFinite := lt_of_lt_of_le hpq le_top
  obtain ⟨B, hBm, hB, hlim⟩ := compact_support_finite_approximation q K hne hc r hr
  let s (n : ℕ) := finiteSupport (B n)
  have hs (n : ℕ) : 0 ≤ s n := finiteSupport_nonnegative _
  have hsm : Monotone s := fun _ _ hnm => finiteSupport_mono (hBm hnm)
  have hpoint (φ : Dual E) : IsLUB (Set.range fun n => fvlFunction (s n) φ) (support K φ) := by
    apply isLUB_of_tendsto_atTop
      (fun n m hnm => ((ofFVL q).monotone (hsm hnm)) φ)
    have hh := ((freeEvalCLM q φ).continuous.tendsto r).comp hlim
    change Tendsto (fun n => ofFVL q (s n) φ) atTop (𝓝 (r φ)) at hh
    simpa only [hr] using hh
  have hupper (n : ℕ) : ofFVL q (s n) ≤ r := by
    intro φ
    change fvlFunction (finiteSupport (B n)) φ ≤ r φ
    rw [finiteSupport_support _ (hB n).1, hr]
    exact support_mono_compact (hB n).1.to_set hc (hB n).2 φ
  have : Nontrivial E := by
    by_contra h
    have : Subsingleton E := not_nontrivial_iff_subsingleton.mp h
    have hz : support K = (fun _ : Dual E => 0) := by
      funext φ
      have heq : (fun x : E => |φ x|) '' K = {0} := by
        ext t
        constructor
        · rintro ⟨x, _, rfl⟩
          simp [Subsingleton.elim x 0]
        · rintro rfl
          exact ⟨0, hac.1.zero_mem hne, by simp⟩
      simp only [support, compactSupport, heq, csSup_singleton]
    rw [hz, freeNormExt_zero] at hinf
    exact ENNReal.zero_ne_top hinf
  obtain ⟨e, he⟩ := exists_norm_eq E (c := 2) (by norm_num)
  let f (n : ℕ) : FVL E := (|FVLv.of e| - s n) ⊔ 0
  let G : Free q E := (|delta q e| - r) ⊔ 0
  have hform (t : Exponent) (n : ℕ) :
      ofFVL t (f n) = (|delta t e| - ofFVL t (s n)) ⊔ 0 := by
    simp only [f, SupHomClass.map_sup, map_sub, VecLatHom.map_abs, ofFVL_of, map_zero]
  refine ⟨f, fun _ => le_sup_right, ?_, G, ?_, ?_, ?_⟩
  · have hh := compact_support_order_null p hp K hne hac hc hinf
      (fun n => ofFVL p (s n)) (fun n => (ofFVL p).map_nonneg (hs n))
      ((ofFVL p).monotone.comp hsm) hpoint e
    simpa only [hform] using hh
  · apply lt_iff_le_not_ge.mpr
    refine ⟨le_sup_right, fun hG => ?_⟩
    have hle : |delta q e| ≤ r := sub_nonpos.mp (sup_le_iff.mp hG).1
    have hn := norm_le_norm_of_abs_le_abs (hle.trans (le_abs_self _))
    rw [(delta q).norm_map, he] at hn
    linarith
  · simp_rw [inclusion_ofFVL, hform]
    exact (tendsto_const_nhds.sub hlim).sup_nhds tendsto_const_nhds
  · intro n
    rw [inclusion_ofFVL, hform]
    exact sup_le_sup (sub_le_sub_left (hupper n) _) le_rfl

end FBLOrderContinuousLH
