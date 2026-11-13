/-
Copyright (c) 2026 Raúl E. Pariente-Martín, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raúl E. Pariente-Martín, Pedro Tradacete
-/

module

public import LeanPool.FBLOrderContinuity.ConvexityBound
public import LeanPool.FBLOrderContinuity.HilbertComparison
public import LeanPool.FBLOrderContinuity.ParameterWitness
public import LeanPool.FBLOrderContinuity.BanLat.OrderDense
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Order.Cofinal



/-!
# Comparison of convexity parameters

This module formalizes Section 5. For p < q, `cross_parameter_inclusion` proves the
eight equivalent conditions listed in `parameterConditions`: order continuity,
sequential order continuity, surjectivity, equivalence of the algebraic free norms,
q-convexity, majorization, order density, and containment of q-compact disks in
p-compact disks. The target exponent may be infinity.

`cross_parameter_witness` constructs a compact support and a decreasing algebraic
sequence when surjectivity fails. `cross_parameter_above_two` adds finite-dimensionality
to the equivalences when q > 2. In contrast, `cross_parameter_hilbert` proves that the
canonical maps for ell-two are lattice isomorphisms when 1 ≤ p < q ≤ 2.

The helper modules `ParameterWitness`, `HilbertComparison`, `EuclideanFamilies`, and
`ConvexityBound` contain the geometric and analytic arguments used here. The auxiliary
`relative_compactness_criterion` retains a reformulation commented out in the revised paper.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal Topology
open Filter Set
universe u v
namespace FBLOrderContinuousLH

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A specified canonical map is a bounded lattice isomorphism onto the target. -/
def IsOntoLatticeIsomorphism {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [NormedVectorLattice X]
    [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [NormedVectorLattice Y]
    (T : LatticeOperator X Y) : Prop :=
  ∃ U : VecLatEquiv X Y, (∀ x, U x = T x) ∧ Continuous U ∧ Continuous U.symm

/-- Section 5: two-sided equivalence of the actual norms on the same FVL. -/
def NormsEquivalentOnFVL (p q : Exponent) (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ v : FVL E,
    c * ‖ofFVL p v‖ ≤ ‖ofFVL q v‖ ∧ ‖ofFVL q v‖ ≤ C * ‖ofFVL p v‖

/-- The eight conditions of Theorem 5.1, in the paper’s order:

1. Order continuity of the canonical inclusion.
2. Sequential order continuity.
3. Surjectivity.
4. Equivalence of the p- and q-free norms on `FVL E`.
5. q-convexity of `Free p E`.
6. Majorization by the range (`IsCofinal`).
7. Order density of the range (`IsOrderDense`).
8. Containment of every q-compact disk in some p-compact disk.

`cross_parameter_inclusion` proves their equivalence for a Banach space and p < q,
including q = ∞. `List.TFAE.out` uses the same indices starting at 1 as the list above. -/
def parameterConditions (p q : Exponent) (hpq : p ≤ q) (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] : List Prop := [
  IsOrderContinuousOp (inclusion (E := E) hpq).toContinuousLinearMap.toLinearMap,
  SigmaOrderContinuous (inclusion (E := E) hpq),
  Function.Surjective (inclusion (E := E) hpq),
  NormsEquivalentOnFVL p q E,
  IsPConvex q (Free p E),
  IsCofinal (Set.range (inclusion (E := E) hpq)),
  IsOrderDense (Set.range (inclusion (E := E) hpq)),
  ∀ K : Set E, IsPCompactDisk q K → ∃ L : Set E, IsPCompactDisk p L ∧ K ⊆ L]

/-- Section 5: the canonical chain of free-norm inequalities. -/
theorem parameter_norm_inequalities {p q : Exponent} (hpq : p ≤ q) (v : FVL E) :
    ‖ofFVL Exponent.infinity v‖ ≤ ‖ofFVL q v‖ ∧ ‖ofFVL q v‖ ≤ ‖ofFVL p v‖ :=
  ⟨norm_ofFVL_infinity_le q v, norm_ofFVL_mono hpq v⟩

/-- Proposition 5.2 (`prop:cross-parameter-witness`): nonsurjectivity for p < q
gives a nonempty absolutely convex compact K whose support has q-free norm at most
one but infinite p-free norm. It also gives a positive algebraic sequence decreasing
to zero in the source with a strictly positive norm limit of its images. The
construction includes q = ∞. -/
theorem cross_parameter_witness [CompleteSpace E] (p q : Exponent) (hpq : p < q)
    (honto : ¬ Function.Surjective (inclusion (E := E) hpq.le)) :
    (∃ K : Set E, K.Nonempty ∧ AbsConvex ℝ K ∧ IsCompact K ∧
      ∃ r : Free q E, (∀ φ, r φ = support K φ) ∧
        0 ≤ r ∧ ‖r‖ ≤ 1 ∧ freeNormExt p (support K) = ⊤) ∧
    FVLFailureWitness p q (inclusion (E := E) hpq.le) := by
  obtain ⟨K, hne, hac, hc, r, hr, hpos, hnorm, hinf⟩ :=
    parameter_support_separation hpq.le honto
  exact ⟨⟨K, hne, hac, hc, r, hr, hpos, hnorm, hinf⟩,
    parameter_failure_witness hpq K hne hac hc r hr hnorm hinf⟩

private theorem inclusion_surjective_iff_boundedBelow {p q : Exponent} (hpq : p ≤ q) :
    Function.Surjective (inclusion (E := E) hpq) ↔
      BoundedBelow (inclusion (E := E) hpq) := by
  rw [embedding_iff]
  constructor
  · intro h
    exact ⟨(inclusion_properties hpq).2.1, by rw [Set.range_eq_univ.mpr h]; exact isClosed_univ⟩
  · rintro ⟨_, hc⟩
    rw [← Set.range_eq_univ, ← hc.closure_eq]
    exact (inclusion_properties hpq).2.2.1.closure_range

private theorem inclusion_qConvex_of_surjective {p q : Exponent} (hpq : p ≤ q)
    (honto : Function.Surjective (inclusion (E := E) hpq)) : IsPConvex q (Free p E) := by
  obtain ⟨c, hc, hb⟩ := (inclusion_surjective_iff_boundedBelow hpq).mp honto
  let C := max 1 c⁻¹
  have hbound (f : Free p E) : ‖f‖ ≤ C * ‖inclusion hpq f‖ := by
    have hh := mul_le_mul_of_nonneg_left (hb f) (inv_nonneg.mpr hc.le)
    have hh' : ‖f‖ ≤ c⁻¹ * ‖inclusion hpq f‖ := by
      simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  refine ⟨C, le_max_left _ _, fun n f => ?_⟩
  have hmap : inclusion hpq (latticePSum q f) =
      latticePSum q (fun i => inclusion hpq (f i)) := by
    apply Subtype.ext
    apply Subtype.ext
    funext φ
    rw [inclusion_apply, latticePSum_apply, latticePSum_apply]
    simp only [inclusion_apply]
  have hnorm (i : Fin n) : ‖inclusion hpq (f i)‖ ≤ ‖f i‖ :=
    ((inclusion hpq).toContinuousLinearMap.le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (inclusion_properties hpq).1)
  have hconv := (free_pConvex q).2 n (fun i => inclusion hpq (f i))
  simp only [one_mul] at hconv
  calc
    _ ≤ C * ‖inclusion hpq (latticePSum q f)‖ := hbound _
    _ = C * ‖latticePSum q (fun i => inclusion hpq (f i))‖ := by rw [hmap]
    _ ≤ C * scalarPSum q (fun i => ‖inclusion hpq (f i)‖) :=
      mul_le_mul_of_nonneg_left hconv (le_trans zero_le_one (le_max_left _ _))
    _ ≤ C * scalarPSum q (fun i => ‖f i‖) :=
      mul_le_mul_of_nonneg_left
        (scalarPSum_mono_abs q _ _ (fun i => by simpa only [abs_norm] using hnorm i))
        (le_trans zero_le_one (le_max_left _ _))

private theorem inclusion_surjective_of_qConvex {p q : Exponent} (hpq : p ≤ q)
    (h : IsPConvex q (Free p E)) : Function.Surjective (inclusion (E := E) hpq) := by
  obtain ⟨S, hS, _, _⟩ := universal_property q h (delta p (E := E)).toContinuousLinearMap
  let J := inclusion (E := E) hpq
  let A : LatticeOperator (Free q E) (Free q E) :=
    { toContinuousLinearMap := J.toContinuousLinearMap.comp S.toContinuousLinearMap
      map_sup' := by intro f g; simp only [ContinuousLinearMap.comp_apply, S.map_sup', J.map_sup']
      map_inf' := by intro f g; simp only [ContinuousLinearMap.comp_apply, S.map_inf', J.map_inf'] }
  let I : LatticeOperator (Free q E) (Free q E) :=
    { toContinuousLinearMap := ContinuousLinearMap.id ℝ _
      map_sup' := fun _ _ => rfl
      map_inf' := fun _ _ => rfl }
  have hAI : A = I := latticeOperator_ext_delta q A I (by
    intro x
    change J (S (delta q x)) = delta q x
    rw [hS]
    exact (inclusion_properties hpq).2.2.2 x)
  intro g
  exact ⟨S g, congrArg (fun T : LatticeOperator (Free q E) (Free q E) => T g) hAI⟩

/-- Theorem 5.1 (`thm:cross-parameter-inclusion`): all eight conditions in
`parameterConditions` are equivalent for p < q over a Banach space. In particular,
order continuity of the canonical inclusion is equivalent to its surjectivity.
The proof uses the compact-support witness for the necessary order conditions and
the universal property for the convexity-to-surjectivity implication. -/
theorem cross_parameter_inclusion [CompleteSpace E] (p q : Exponent)
    (hpq : p < q) :
    List.TFAE (parameterConditions p q hpq.le E) := by
  let J := inclusion (E := E) hpq.le
  have hJ : Function.Injective J := (inclusion_properties hpq.le).2.1
  unfold parameterConditions
  tfae_have 1 ↔ 2 := sigma_order_continuity p J.toContinuousLinearMap.toLinearMap
    (fun _ h => J.toVecLatHom.map_nonneg h)
  tfae_have 2 → 3 := by
    intro h
    by_contra honto
    obtain ⟨f, _, hf, G, hG, _, hGlower⟩ := (cross_parameter_witness p q hpq honto).2
    exact hG.not_ge ((h (fun n => ofFVL p (f n)) hf).2.2
      (by rintro _ ⟨n, rfl⟩; exact hGlower n))
  tfae_have 3 → 2 := by
    intro honto f hf
    refine ⟨J.toVecLatHom.monotone.comp_antitone hf.1, ⟨?_, ?_⟩⟩
    · rintro _ ⟨n, rfl⟩
      exact J.toVecLatHom.map_nonneg (hf.2.1 (Set.mem_range_self n))
    · intro b hb
      obtain ⟨a, rfl⟩ := honto b
      have ha : a ≤ 0 := hf.2.2 (by
        rintro _ ⟨n, rfl⟩
        exact J.toVecLatHom.le_of_map_le hJ (hb (Set.mem_range_self n)))
      change J.toVecLatHom a ≤ 0
      simpa only [map_zero] using J.toVecLatHom.monotone ha
  tfae_have 3 → 4 := by
    intro honto
    obtain ⟨c, hc, hb⟩ := (inclusion_surjective_iff_boundedBelow hpq.le).mp honto
    exact ⟨c, 1, hc, zero_lt_one, fun v => ⟨by
      simpa only [inclusion_ofFVL] using hb (ofFVL p v),
      by simpa only [one_mul] using norm_ofFVL_mono hpq.le v⟩⟩
  tfae_have 4 → 3 := by
    rintro ⟨c, C, hc, _, hnorm⟩
    apply (inclusion_surjective_iff_boundedBelow hpq.le).mpr
    refine ⟨c, hc, fun f => ?_⟩
    exact (denseRange_ofFVL p).induction_on f
      (isClosed_le (continuous_const.mul continuous_norm) J.toContinuousLinearMap.continuous.norm)
      (fun v => by simpa only [inclusion_ofFVL] using (hnorm v).1)
  tfae_have 3 → 5 := inclusion_qConvex_of_surjective hpq.le
  tfae_have 5 → 3 := inclusion_surjective_of_qConvex hpq.le
  tfae_have 3 → 6 := by
    intro honto g
    obtain ⟨f, rfl⟩ := honto g
    exact ⟨J f, Set.mem_range_self f, le_rfl⟩
  tfae_have 6 → 3 := by
    intro hcofinal
    by_contra honto
    obtain ⟨K, _, _, _, r, hr, hrpos, _, hinf⟩ :=
      (cross_parameter_witness p q hpq honto).1
    obtain ⟨_, ⟨f, rfl⟩, hrf⟩ := hcofinal r
    have hbound : freeNormExt p (support K) ≤ freeNormExt p f := by
      apply freeNormExt_mono_abs
      intro φ
      rw [← hr, abs_of_nonneg (hrpos φ)]
      have hh : r φ ≤ f φ := by simpa only [inclusion_apply] using hrf φ
      exact hh.trans (le_abs_self _)
    rw [hinf, freeNormExt_eq_norm] at hbound
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hbound)
  tfae_have 3 → 7 := by
    intro honto
    rw [Set.range_eq_univ.mpr honto]
    exact IsOrderDense.univ
  tfae_have 7 → 3 := by
    intro hdense
    by_contra honto
    obtain ⟨f, _, hf, G, hG, _, hGlower⟩ := (cross_parameter_witness p q hpq honto).2
    obtain ⟨_, ⟨u, rfl⟩, hu, huG⟩ := hdense hG
    have hu0 : u ≤ 0 := hf.2.2 (by
      rintro _ ⟨n, rfl⟩
      exact J.toVecLatHom.le_of_map_le hJ (huG.trans (hGlower n)))
    apply hu.not_ge
    change J.toVecLatHom u ≤ 0
    simpa only [map_zero] using J.toVecLatHom.monotone hu0
  tfae_have 3 → 8 := by
    intro honto K hK
    obtain ⟨r, hr⟩ := pCompact_support_inFree q K hK
    obtain ⟨f, hf⟩ := honto r
    obtain ⟨L, hL, hdom⟩ := summable_global_domination p f
    obtain ⟨hLne, hLa, hLc⟩ := summable_disk_compact p L hL
    have hKc := (summable_disk_compact q K hK).2.2
    refine ⟨L, hL, fun x hx => mem_of_abs_eval_le_support L hLne hLa hLc.isClosed x ?_⟩
    intro φ
    have hpoint : f φ = support K φ :=
      (inclusion_apply hpq.le f φ).symm.trans
        ((congrArg (fun g : Free q E => g φ) hf).trans (hr φ))
    calc
      |φ x| ≤ support K φ :=
        le_csSup (hKc.image φ.continuous.abs).bddAbove (Set.mem_image_of_mem _ hx)
      _ ≤ |f φ| := by rw [← hpoint]; exact le_abs_self _
      _ ≤ support L φ := hdom φ
  tfae_have 8 → 6 := by
    intro hdisks g
    obtain ⟨K, hK, hg⟩ := summable_global_domination q g
    obtain ⟨L, hL, hKL⟩ := hdisks K hK
    obtain ⟨f, hf⟩ := pCompact_support_inFree p L hL
    obtain ⟨hKne, _, _⟩ := summable_disk_compact q K hK
    have hLc := (summable_disk_compact p L hL).2.2
    refine ⟨J f, Set.mem_range_self f, fun φ => ?_⟩
    rw [show J f φ = f φ from inclusion_apply hpq.le f φ, hf]
    apply ((le_abs_self _).trans (hg φ)).trans
    apply csSup_le (hKne.image _)
    rintro _ ⟨x, hx, rfl⟩
    exact le_csSup (hLc.image φ.continuous.abs).bddAbove (Set.mem_image_of_mem _ (hKL hx))
  tfae_finish

/-- Auxiliary reformulation using relatively compact sets (commented out in the revised paper). -/
theorem relative_compactness_criterion [CompleteSpace E] (p q : Exponent)
    (hpq : p < q) :
    IsCofinal (Set.range (inclusion (E := E) hpq.le)) ↔
      ∀ A : Set E, IsRelativelyPCompact q A → IsRelativelyPCompact p A := by
  have hi : IsCofinal (Set.range (inclusion (E := E) hpq.le)) ↔
      ∀ K : Set E, IsPCompactDisk q K → ∃ L : Set E, IsPCompactDisk p L ∧ K ⊆ L :=
    (cross_parameter_inclusion (E := E) p q hpq).out 6 8
  rw [hi]
  constructor
  · intro h A ⟨K, hK, hAK⟩
    obtain ⟨L, hL, hKL⟩ := h K hK
    exact ⟨L, hL, hAK.trans hKL⟩
  · intro h K hK
    exact h K ⟨K, hK, Set.Subset.rfl⟩

private theorem one_norm_le_of_norming_family {n : ℕ} (x : Fin n → E)
    (C : ℝ) (hC : 0 < C) (hx : ∀ i, ‖x i‖ ≤ 1)
    (hnorm : ∀ φ : Dual E, ‖φ‖ ≤ C * scalarPSum Exponent.infinity (fun i => φ (x i)))
    (v : FVL E) :
    ‖ofFVL Exponent.one v‖ ≤ C * n * ‖ofFVL Exponent.infinity v‖ := by
  have hsum_one {m : ℕ} (a : Fin m → ℝ) : scalarPSum Exponent.one a = ∑ i, |a i| := by
    simp [scalarPSum, Exponent.one]
  have hfamily {m : ℕ} (φ : Fin m → Dual E) (hφ : NormAdmissible Exponent.one φ) :
      ∑ j, ‖φ j‖ ≤ C * n := by
    calc
      _ ≤ ∑ j, C * ∑ i, |φ j (x i)| := by
        apply Finset.sum_le_sum
        intro j _
        apply (hnorm (φ j)).trans
        apply mul_le_mul_of_nonneg_left _ hC.le
        rw [← hsum_one]
        exact scalarPSum_mono_exponent
          (show Exponent.one ≤ Exponent.infinity from (show (1 : ℝ≥0∞) ≤ ⊤ from le_top)) _
      _ = C * ∑ i, ∑ j, |φ j (x i)| := by rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ C * ∑ _ : Fin n, (1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        apply Finset.sum_le_sum
        intro i _
        simpa only [hsum_one] using
          (normAdmissible_eval_le_norm Exponent.one φ hφ (x i)).trans (hx i)
      _ = C * n := by simp
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  rw [← freeNormExt_eq_norm]
  change (⨆ m, ⨆ φ : Fin m → Dual E, ⨆ (_ : NormAdmissible Exponent.one φ),
    ENNReal.ofReal (scalarPSum Exponent.one (fun j => ofFVL Exponent.one v (φ j)))) ≤ _
  refine iSup_le fun m => iSup_le fun φ => iSup_le fun hφ => ENNReal.ofReal_le_ofReal ?_
  rw [hsum_one]
  calc
    _ ≤ ∑ j, ‖φ j‖ * ‖ofFVL Exponent.infinity v‖ := by
      apply Finset.sum_le_sum
      intro j _
      have hh := hp_apply_abs_le Exponent.infinity (ofFVL Exponent.infinity v).1 (φ j)
      change |ofFVL Exponent.infinity v (φ j)| ≤ ‖φ j‖ * ‖ofFVL Exponent.infinity v‖ at hh
      simpa only [(model_evaluation Exponent.infinity (0 : E) _ _).2,
        (model_evaluation Exponent.one (0 : E) _ _).2] using hh
    _ = (∑ j, ‖φ j‖) * ‖ofFVL Exponent.infinity v‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ C * n * ‖ofFVL Exponent.infinity v‖ :=
      mul_le_mul_of_nonneg_right (hfamily φ hφ) (norm_nonneg _)

/-- Equation (5.1): a finite-dimensional space has a finite family in its
unit ball that norms the dual up to a positive constant C. The same family bounds
the one-free norm by C times its cardinality times the infinity-free norm.
Indexing by `Fin (m + 1)` records that the norming family is nonempty. -/
theorem finite_dimensional_norming_family [FiniteDimensional ℝ E] :
    ∃ (m : ℕ) (x : Fin (m + 1) → E) (C : ℝ), 0 < C ∧ (∀ i, ‖x i‖ ≤ 1) ∧
      (∀ φ : Dual E, ‖φ‖ ≤ C * scalarPSum Exponent.infinity (fun i => φ (x i))) ∧
      ∀ v : FVL E, ‖ofFVL Exponent.one v‖ ≤
        C * (m + 1 : ℝ) * ‖ofFVL Exponent.infinity v‖ := by
  classical
  let K := Metric.closedBall (0 : E) 1
  have hKne : K.Nonempty := ⟨0, by simp [K]⟩
  have hKac : AbsConvex ℝ K := ⟨balanced_closedBall_zero, convex_closedBall _ _⟩
  obtain ⟨A, hKA, hAK⟩ := outer_polytope_approximation K hKne hKac
    (isCompact_closedBall _ _) inferInstance 1 zero_lt_one
  have hA : A.Nonempty := by
    by_contra h
    have hzero := hKA hKne.some_mem
    simp only [Finset.not_nonempty_iff_eq_empty.mp h, Finset.coe_empty,
      absConvexHull_empty, Set.mem_empty_iff_false] at hzero
  let m := A.card - 1
  have hcard : A.card = m + 1 := (Nat.sub_add_cancel (Finset.card_pos.mpr hA)).symm
  let e : A ≃ Fin (m + 1) := Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hcard)
  let x (i : Fin (m + 1)) : E := (1 / 2 : ℝ) • (e.symm i : E)
  have hx (i : Fin (m + 1)) : ‖x i‖ ≤ 1 := by
    obtain ⟨y, hy, heq⟩ := hAK (subset_absConvexHull (e.symm i).2)
    have hy' : ‖y‖ ≤ 1 := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hy
    have hxy : x i = y := by
      change (1 / 2 : ℝ) • (e.symm i : E) = y
      rw [← heq, smul_smul]
      norm_num
    simpa only [hxy] using hy'
  have hnorm (φ : Dual E) : ‖φ‖ ≤ 2 * scalarPSum Exponent.infinity (fun i => φ (x i)) := by
    apply φ.opNorm_le_of_unit_norm (mul_nonneg (by norm_num) (scalarPSum_nonneg _ _))
    intro y hy
    apply absConvexHull_eval_bound (A : Set E) φ _ ?_ y
      (hKA (by simpa only [K, Metric.mem_closedBall, dist_zero_right, hy] using le_rfl))
    intro a ha
    let i := e ⟨a, ha⟩
    have hval : |φ a| = 2 * |φ (x i)| := by
      simp [x, i, map_smul, smul_eq_mul, abs_mul]
    rw [hval]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [scalarPSum_eq_piLp_norm]
    exact PiLp.norm_apply_le (WithLp.toLp ⊤ (fun i => φ (x i))) i
  refine ⟨m, x, 2, by norm_num, hx, hnorm, fun v => ?_⟩
  simpa only [Nat.cast_add, Nat.cast_one] using
    one_norm_le_of_norming_family x 2 (by norm_num) hx hnorm v

/-- Equation (5.1): over a finite-dimensional space, the one-free norm is bounded
by a fixed positive multiple of the infinity-free norm on the algebraic core.
The zero-dimensional case is included. Together with monotonicity, this makes
all free norms equivalent in finite dimension. -/
theorem finite_dimensional_norm_comparison [FiniteDimensional ℝ E] :
    ∃ C : ℝ, 0 < C ∧ ∀ v : FVL E,
      ‖ofFVL Exponent.one v‖ ≤ C * ‖ofFVL Exponent.infinity v‖ := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    let := h
    refine ⟨1, zero_lt_one, fun v => ?_⟩
    have hz : ofFVL Exponent.one v = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      funext φ
      have hφ : φ = 0 := by
        ext x
        simp [Subsingleton.elim x 0]
      subst φ
      change ofFVL Exponent.one v (0 : Dual E) = 0
      have hh := (ofFVL Exponent.one v).1.2.1 0 (le_refl 0) (0 : Dual E)
      simpa using hh
    rw [hz, norm_zero, one_mul]
    exact norm_nonneg _
  | inr h =>
    let := h
    obtain ⟨m, x, C, hC, _, _, hnorm⟩ := finite_dimensional_norming_family (E := E)
    exact ⟨C * (m + 1), mul_pos hC (by positivity), hnorm⟩

private theorem finite_dimensional_normsEquivalent [FiniteDimensional ℝ E]
    {p q : Exponent} (hpq : p ≤ q) : NormsEquivalentOnFVL p q E := by
  obtain ⟨C, hC, hnorm⟩ := finite_dimensional_norm_comparison (E := E)
  refine ⟨C⁻¹, 1, inv_pos.mpr hC, zero_lt_one, fun v => ⟨?_, ?_⟩⟩
  · have hv : ‖ofFVL p v‖ ≤ C * ‖ofFVL q v‖ := by
      calc
        _ ≤ ‖ofFVL Exponent.one v‖ :=
          norm_ofFVL_mono (show Exponent.one ≤ p from p.2) v
        _ ≤ C * ‖ofFVL Exponent.infinity v‖ := hnorm v
        _ ≤ C * ‖ofFVL q v‖ :=
          mul_le_mul_of_nonneg_left (norm_ofFVL_infinity_le q v) hC.le
    have hh := mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hC.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] using hh
  · simpa only [one_mul] using norm_ofFVL_mono hpq v

/-- For infinite-dimensional E and finite p, q-convexity of `Free p E` forces
`q ≤ max 2 p`. Euclidean dual families prove the obstruction when p ≥ 2; the
general case transfers convexity through the inclusion at `max 2 p`. This is
the geometric bound used in Corollary 5.3, also excluding q = ∞. -/
theorem convexity_parameter_bound (hE : ¬ FiniteDimensional ℝ E)
    (p q : Exponent) (hp : p.IsFinite) (h : IsPConvex q (Free p E)) :
    q ≤ max Exponent.two p := by
  by_contra! hq
  let r := max Exponent.two p
  have hpr : p ≤ r := le_max_right _ _
  have hrq : r ≤ q := hq.le
  have hpq : p ≤ q := hpr.trans hrq
  have honto := inclusion_surjective_of_qConvex hpq h
  have honto' : Function.Surjective (inclusion (E := E) hrq) := by
    intro g
    obtain ⟨f, hf⟩ := honto g
    refine ⟨inclusion hpr f, ?_⟩
    have hcomp : inclusion hrq (inclusion hpr f) = inclusion hpq f := by
      apply Subtype.ext
      apply Subtype.ext
      funext φ
      simp only [inclusion_apply]
    exact hcomp.trans hf
  have hrfinite : r.IsFinite := by
    change max (2 : ℝ≥0∞) p.1 < ⊤
    exact max_lt (by norm_num) hp
  exact (not_le_of_gt hq) (ConvexityBound.parameter_bound_ge_two hE r q hrfinite
    (le_max_left _ _) (inclusion_qConvex_of_surjective hrq honto'))

/-- Corollary 5.3 (`cor:cross-parameter-above-two`): for p < q and q > 2, finite
dimensionality of E is equivalent to all eight conditions of Theorem 5.1. Thus
an infinite-dimensional space has a nonsurjective, non-order-continuous inclusion
for these exponents. The target q may be ∞. -/
theorem cross_parameter_above_two [CompleteSpace E] (p q : Exponent)
    (hpq : p < q) (h2 : Exponent.two < q) :
    List.TFAE (FiniteDimensional ℝ E :: parameterConditions p q hpq.le E) := by
  have ht := cross_parameter_inclusion (E := E) p q hpq
  have heq : FiniteDimensional ℝ E ↔ IsPConvex q (Free p E) := by
    constructor
    · intro h
      let := h
      exact (ht.out 4 5).mp (finite_dimensional_normsEquivalent hpq.le)
    · intro h
      by_contra hE
      exact (not_le_of_gt (max_lt h2 hpq))
        (convexity_parameter_bound hE p q (lt_of_lt_of_le hpq le_top) h)
  exact (List.tfae_cons (b := IsPConvex q (Free p E))
    (by simp [parameterConditions])).mpr ⟨heq, ht⟩

private theorem inclusion_onto_lattice_isomorphism {p q : Exponent} (hpq : p ≤ q)
    (honto : Function.Surjective (inclusion (E := E) hpq)) :
    IsOntoLatticeIsomorphism (inclusion (E := E) hpq) := by
  let J := inclusion (E := E) hpq
  let e := ContinuousLinearEquiv.ofBijective J.toContinuousLinearMap
    (LinearMap.ker_eq_bot.mpr (inclusion_properties hpq).2.1)
    (LinearMap.range_eq_top.mpr honto)
  let U : VecLatEquiv (Free p E) (Free q E) :=
    { e.toLinearEquiv with map_sup' := J.map_sup', map_inf' := J.map_inf' }
  exact ⟨U, fun _ => rfl, e.continuous, e.symm.continuous⟩

/-- The real Hilbert sequence space used in Remark 5.4. -/
abbrev HilbertSequence : Type := lp (fun _ : ℕ => ℝ) 2

/-- Remark 5.4 (`rem:cross-parameter-hilbert`): for the real Hilbert sequence space
ell-two and 1 ≤ p < q ≤ 2, the canonical inclusion is a bounded lattice isomorphism
onto the target and is order continuous. The uniform comparison of the one-free
and two-free norms with constant 3 gives the required equivalence for intermediate
exponents. This shows why the condition q > 2 in Corollary 5.3 is essential. -/
theorem cross_parameter_hilbert (p q : Exponent) (hpq : p < q) (hq : q ≤ Exponent.two) :
    IsOntoLatticeIsomorphism (inclusion (E := HilbertSequence) hpq.le) ∧
    IsOrderContinuousOp
      (inclusion (E := HilbertSequence) hpq.le).toContinuousLinearMap.toLinearMap := by
  suffices hcomparison : ∃ C : ℝ, 0 < C ∧ ∀ v : FVL HilbertSequence,
      ‖ofFVL Exponent.one v‖ ≤ C * ‖ofFVL Exponent.two v‖ by
    obtain ⟨C, hC, hcomparison⟩ := hcomparison
    have hnorms : NormsEquivalentOnFVL p q HilbertSequence := by
      refine ⟨C⁻¹, 1, inv_pos.mpr hC, zero_lt_one, fun v => ⟨?_, ?_⟩⟩
      · have hv : ‖ofFVL p v‖ ≤ C * ‖ofFVL q v‖ := by
          calc
            _ ≤ ‖ofFVL Exponent.one v‖ := norm_ofFVL_mono (show Exponent.one ≤ p from p.2) v
            _ ≤ C * ‖ofFVL Exponent.two v‖ := hcomparison v
            _ ≤ C * ‖ofFVL q v‖ := mul_le_mul_of_nonneg_left (norm_ofFVL_mono hq v) hC.le
        have hh := mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hC.le)
        simpa only [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] using hh
      · simpa only [one_mul] using norm_ofFVL_mono hpq.le v
    have ht := cross_parameter_inclusion (E := HilbertSequence) p q hpq
    have honto : Function.Surjective (inclusion (E := HilbertSequence) hpq.le) :=
      (ht.out 3 4).mpr hnorms
    exact ⟨inclusion_onto_lattice_isomorphism hpq.le honto,
      (ht.out 1 3 (a := IsOrderContinuousOp
        (inclusion (E := HilbertSequence) hpq.le).toContinuousLinearMap.toLinearMap)).mpr honto⟩
  exact ⟨3, by norm_num, HilbertComparison.hilbert_free_norm_comparison⟩

end FBLOrderContinuousLH
