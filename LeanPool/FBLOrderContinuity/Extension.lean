/-
Copyright (c) 2026 Raúl E. Pariente-Martín, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raúl E. Pariente-Martín, Pedro Tradacete
-/

module

public import LeanPool.FBLOrderContinuity.Support
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import LeanPool.FBLOrderContinuity.LpExtension
public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule
public import Mathlib.Topology.PartitionOfUnity



/-!
# Operator extension and order continuity

This module proves the operator-extension characterizations in Sections 1 and 4 of
the paper. `POEWith p E M C` asserts that M is closed in E and uses one extension
constant for every dimension and every operator from M into finite-dimensional ell-p.
`HasPOE p E M` allows any such constant for the same ambient-space/subspace pair.

For finite p, `poe_inclusion` identifies order continuity, sequential order continuity,
a lower free-norm bound, and POE for a closed subspace. Failure gives an explicit
`FVLFailureWitness`. `intro_poe` and `all_parameter_characterization` pass from
subspace inclusions to arbitrary operators; the latter includes p = infinity.

Applications cover complemented and locally complemented subspaces, the canonical
bidual embedding, embeddings of C(K), the uncomplemented inclusion of c0 into ell-infinity,
and separably injective spaces. `LpExtension` supplies the sharp finite-target
Hahn–Banach argument, while `Support` supplies compact geometric witnesses.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal Topology
open Filter Set
universe u v w
namespace FBLOrderContinuousLH

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Finite-dimensional ell_p, using Mathlib's actual p-norm. -/
abbrev FiniteLp (p : Exponent) (n : ℕ) := PiLp p.1 (fun _ : Fin n => ℝ)

/-- The quantitative POE-p property for the explicit pair E and M ⊆ E. The subspace M
is closed in E, and one constant C ≥ 1 bounds extensions to E of every operator from M
into any finite-dimensional ell-p space, with norm at most C times the original norm. -/
def POEWith (p : Exponent) (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Submodule ℝ E) (C : ℝ) : Prop :=
  IsClosed (M : Set E) ∧ 1 ≤ C ∧ ∀ (n : ℕ) (R : M →L[ℝ] FiniteLp p n),
    ∃ S : E →L[ℝ] FiniteLp p n, S.comp M.subtypeL = R ∧ ‖S‖ ≤ C * ‖R‖

/-- The POE-p property for the explicit pair E and M ⊆ E: M is closed in E and some
constant C ≥ 1 works for all finite-dimensional ell-p targets, as specified by `POEWith`. -/
def HasPOE (p : Exponent) (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Submodule ℝ E) : Prop := ∃ C, POEWith p E M C

/-- The subspace in a quantitative POE pair is closed in the specified ambient space. -/
theorem POEWith.isClosed {p : Exponent} {M : Submodule ℝ E} {C : ℝ}
    (h : POEWith p E M C) : IsClosed (M : Set E) := h.1

/-- The subspace in a POE pair is closed in the specified ambient space. -/
theorem HasPOE.isClosed {p : Exponent} {M : Submodule ℝ E}
    (h : HasPOE p E M) : IsClosed (M : Set E) := h.choose_spec.isClosed

/-- An explicit obstruction to sequential order continuity: positive algebraic elements
decrease to zero in the source, but their images converge in norm to a strictly positive
target element G. Every image also dominates G, so the image sequence cannot decrease
to zero in order. Used in Theorem 4.1 and Propositions 4.12 and 5.2. -/
def FVLFailureWitness (p q : Exponent) (T : LatticeOperator (Free p F) (Free q E)) : Prop :=
  ∃ f : ℕ → FVL F, (∀ n, 0 ≤ f n) ∧
    DecreasesToZero (fun n => ofFVL p (f n)) ∧
    ∃ G : Free q E, 0 < G ∧
      Tendsto (fun n => T (ofFVL p (f n))) atTop (𝓝 G) ∧
      ∀ n, G ≤ T (ofFVL p (f n))

/-- Section 4: regularity of a specified vector sublattice. -/
def IsRegularSublattice {X : Type u} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (Y : VectorSublattice X) : Prop :=
  IsOrderContinuousOp Y.subtype.toLinearMap

/-- The algebraic range sublattice of an induced map, before taking any norm closure. -/
def inducedRange (p : Exponent) (T : F →L[ℝ] E) : VectorSublattice (Free p E) where
  toSubmodule := (induced p T).toContinuousLinearMap.toLinearMap.range
  sup_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f ⊔ g, (induced p T).map_sup' f g⟩

private theorem poe_norm_bound (p : Exponent) (M : Submodule ℝ E) (C : ℝ)
    (h : POEWith p E M C) (f : Free p M) :
    ‖f‖ ≤ C * ‖induced p M.subtypeL f‖ := by
  obtain ⟨_, h⟩ := h
  have hC : 0 < C := zero_lt_one.trans_le h.1
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le (norm_nonneg _))).mp
  rw [← freeNormExt_eq_norm p f, freeNormExt]
  split_ifs with htop
  · refine iSup_le fun ψ => iSup_le fun hψ => ?_
    obtain ⟨φ, hφ, hφnorm⟩ := exists_extension_norm_eq M ψ
    have hcomp : φ.comp M.subtypeL = ψ := ContinuousLinearMap.ext hφ
    calc
      ENNReal.ofReal |f ψ| ≤ freeNormExt p (induced p M.subtypeL f) := by
        rw [freeNormExt, ite_eq_left htop]
        exact le_iSup_of_le φ (le_iSup_of_le (hφnorm ▸ hψ)
          (by rw [canonical_map_formulas, hcomp]))
      _ ≤ ENNReal.ofReal (C * ‖induced p M.subtypeL f‖) := by
        rw [freeNormExt_eq_norm]
        exact ENNReal.ofReal_le_ofReal
          (by simpa only [one_mul] using
            mul_le_mul_of_nonneg_right h.1 (norm_nonneg (induced p M.subtypeL f)))
  · refine iSup_le fun n => iSup_le fun ψ => iSup_le fun hψ => ?_
    let R : M →L[ℝ] FiniteLp p n :=
      (PiLp.continuousLinearEquiv p.1 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi ψ)
    have hR : ‖R‖ ≤ 1 := by
      apply R.opNorm_le_bound zero_le_one
      intro x
      change ‖WithLp.toLp p.1 (fun i => ψ i x)‖ ≤ 1 * ‖x‖
      simpa only [one_mul, scalarPSum_eq_piLp_norm] using
        normAdmissible_eval_le_norm p ψ hψ x
    obtain ⟨S, hS, hSnorm⟩ := h.2 n R
    let φ (i : Fin n) : Dual E := (PiLp.proj p.1 (fun _ : Fin n => ℝ) i).comp S
    have hφ (i : Fin n) : (φ i).comp M.subtypeL = ψ i := by
      apply ContinuousLinearMap.ext
      intro x
      exact congrArg (fun L : M →L[ℝ] FiniteLp p n => (L x) i) hS
    have hSnorm' : ‖S‖ ≤ C :=
      hSnorm.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hR hC.le)
    have hb := freeNorm_scaled_family_le p (induced p M.subtypeL f) φ hC (by
      intro x hx
      rw [scalarPSum_eq_piLp_norm]
      change ‖S x‖ ≤ C
      exact (S.le_opNorm x).trans
        ((mul_le_mul hSnorm' hx (norm_nonneg x) hC.le).trans_eq (mul_one C)))
    simp only [canonical_map_formulas, hφ] at hb
    exact ENNReal.ofReal_le_ofReal hb

private theorem boundedBelow_of_poe (p : Exponent) (M : Submodule ℝ E)
    (h : HasPOE p E M) : BoundedBelow (induced p M.subtypeL) := by
  obtain ⟨C, hC⟩ := h
  have hpos : 0 < C := zero_lt_one.trans_le hC.2.1
  refine ⟨C⁻¹, inv_pos.mpr hpos, fun f => ?_⟩
  have hh := mul_le_mul_of_nonneg_left (poe_norm_bound p M C hC f) (inv_nonneg.mpr hpos.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] using hh

private theorem isometry_of_poe_one (p : Exponent) (M : Submodule ℝ E)
    (h : POEWith p E M 1) : Isometry (induced p M.subtypeL) := by
  apply AddMonoidHomClass.isometry_of_norm (induced p M.subtypeL).toContinuousLinearMap
  intro f
  apply le_antisymm
  · have hnorm : ‖M.subtypeL‖ ≤ 1 := M.subtypeL.opNorm_le_bound zero_le_one
      (fun x => by simp)
    exact ((induced p M.subtypeL).toContinuousLinearMap.le_opNorm f).trans (by
      rw [(induced_norm_generators p M.subtypeL).1]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hnorm (norm_nonneg f))
  · simpa only [one_mul] using poe_norm_bound p M 1 h f

/-- At exponent ∞, coordinatewise Hahn–Banach extension gives POE with constant one.
Each coordinate extends without increasing its norm, and the target maximum norm
combines the extensions. Closedness of M supplies the closed-pair requirement in POE. -/
theorem poe_infinity_one (M : Submodule ℝ E)
    (hM : IsClosed (M : Set E)) : POEWith Exponent.infinity E M 1 := by
  classical
  refine ⟨hM, le_rfl, fun n R => ?_⟩
  let Rcoord (i : Fin n) : Dual M := (PiLp.proj ⊤ (fun _ : Fin n => ℝ) i).comp R
  choose φ hφ hnorm using fun i => exists_extension_norm_eq M (Rcoord i)
  let S : E →L[ℝ] FiniteLp Exponent.infinity n :=
    (PiLp.continuousLinearEquiv ⊤ ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi φ)
  refine ⟨S, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    apply WithLp.ofLp_injective ⊤
    exact funext fun i => hφ i x
  · rw [one_mul]
    apply S.opNorm_le_bound (norm_nonneg R)
    intro x
    change ‖WithLp.toLp ⊤ (fun i => φ i x)‖ ≤ ‖R‖ * ‖x‖
    rw [PiLp.norm_toLp]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg R) (norm_nonneg x))).mpr
    intro i
    have hi : ‖Rcoord i‖ ≤ ‖R‖ := by
      apply (Rcoord i).opNorm_le_bound (norm_nonneg R)
      intro y
      exact (PiLp.norm_apply_le (R y) i).trans (R.le_opNorm y)
    exact ((φ i).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (by simpa only [hnorm] using hi) (norm_nonneg x))

/-- For a closed subspace of a Banach space, POE at p is equivalent to a positive
lower norm bound for the induced free-lattice inclusion. Finite exponents use the
tensor-gauge extension theorem; the endpoint uses coordinatewise Hahn–Banach. -/
theorem poe_iff_boundedBelow (p : Exponent)
    (M : Submodule ℝ E) (hM : IsClosed (M : Set E)) :
    HasPOE p E M ↔ BoundedBelow (induced p M.subtypeL) := by
  constructor
  · exact boundedBelow_of_poe p M
  · intro hb
    rcases lt_or_eq_of_le (le_top : p.1 ≤ ⊤) with hp | hp
    · obtain ⟨c, hc, hb⟩ := hb
      refine ⟨max 1 c⁻¹, hM, le_max_left _ _, fun n R => ?_⟩
      apply FiniteLpExtension.extend_of_free_norm_bound p hp M
        (zero_lt_one.trans_le (le_max_left _ _)) ?_ n R
      intro f
      have hh := mul_le_mul_of_nonneg_left (hb f) (inv_nonneg.mpr hc.le)
      have hf : ‖f‖ ≤ c⁻¹ * ‖induced p M.subtypeL f‖ := by
        simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hh
      exact hf.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    · have heq : p = Exponent.infinity := Subtype.ext hp
      subst p
      exact ⟨1, poe_infinity_one M hM⟩

/-- The sharp version of `poe_iff_boundedBelow`: the pair has extension constant one
exactly when the canonical free-lattice inclusion is isometric. This applies to every
exponent and is used for Banach-space ideals and the canonical bidual pair. -/
theorem poe_one_iff_isometry (p : Exponent)
    (M : Submodule ℝ E) (hM : IsClosed (M : Set E)) :
    POEWith p E M 1 ↔ Isometry (induced p M.subtypeL) := by
  constructor
  · exact isometry_of_poe_one p M
  · intro hi
    rcases lt_or_eq_of_le (le_top : p.1 ≤ ⊤) with hp | hp
    · refine ⟨hM, le_rfl, fun n R =>
        FiniteLpExtension.extend_of_free_norm_bound p hp M zero_lt_one ?_ n R⟩
      intro f
      rw [one_mul, hi.norm_map_of_map_zero (map_zero (induced p M.subtypeL).toContinuousLinearMap)]
    · have heq : p = Exponent.infinity := Subtype.ext hp
      subst p
      exact poe_infinity_one M hM

private theorem section_support_inFree [CompleteSpace E] (p : Exponent) (hp : p.IsFinite)
    (M : Submodule ℝ E) (_hM : IsClosed (M : Set E))
    (hb : BoundedBelow (induced p M.subtypeL)) (K : Set E) (hK : IsPCompactDisk p K) :
    InFree p (support {x : M | (x : E) ∈ K}) := by
  obtain ⟨s, hs, hgen, _⟩ := subsets_summable_disk p hp (K ∩ (M : Set E)) K
    ⟨0, (summable_disk_compact p K hK).2.1.1.zero_mem (summable_disk_compact p K hK).1,
      M.zero_mem⟩ Set.inter_subset_left hK
  have hsub : VectorSublattice.generated (delta p '' (K ∩ (M : Set E))) ≤
      inducedRange p M.subtypeL :=
    VectorSublattice.generated_le (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨delta p (⟨x, hx.2⟩ : M), (induced_norm_generators p M.subtypeL).2 _⟩)
  obtain ⟨l, hl⟩ := VectorSublattice.topologicalClosure_minimal hsub
    ((embedding_iff (induced p M.subtypeL).toContinuousLinearMap).mp hb).2 hgen
  refine ⟨l, fun ψ => ?_⟩
  obtain ⟨φ, hφ, _⟩ := exists_extension_norm_eq M ψ
  calc
    l ψ = s φ := by
      rw [← hl]
      change l ψ = l (φ.comp M.subtypeL)
      exact congrArg l (ContinuousLinearMap.ext hφ).symm
    _ = support (K ∩ (M : Set E)) φ := hs φ
    _ = support {x : M | (x : E) ∈ K} ψ := by
      unfold support
      congr 1
      ext r
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx.2⟩, hx.1, congrArg abs (hφ ⟨x, hx.2⟩).symm⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, ⟨hx, x.2⟩, congrArg abs (hφ x)⟩

/-- Proposition 4.9 (`prop:poe-sufficiency`): a lower norm bound for a closed-subspace
free p-convex Banach lattices inclusion implies order continuity at finite p.
Compact support sections
and positive patches provide the order-theoretic consequence of the norm bound. -/
theorem poe_sufficiency [CompleteSpace E] (p : Exponent) (hp : p.IsFinite)
    (M : Submodule ℝ E) (hM : IsClosed (M : Set E))
    (hb : BoundedBelow (induced p M.subtypeL)) :
    IsOrderContinuousOp (induced p M.subtypeL).toContinuousLinearMap.toLinearMap  := by
  let : CompleteSpace M := hM.isComplete.completeSpace_coe
  apply (orderContinuous_iff_decreasing (induced p M.subtypeL).toContinuousLinearMap.toLinearMap
    (fun _ h => (induced p M.subtypeL).toVecLatHom.map_nonneg h)).mpr
  intro ι _ _ _ f hf
  apply (positive_patches_net p (fun i => induced p M.subtypeL (f i))
    ((induced p M.subtypeL).toVecLatHom.monotone.comp_antitone hf.1)
    (fun i => (induced p M.subtypeL).toVecLatHom.map_nonneg
      (hf.2.1 (Set.mem_range_self i)))).mpr
  rintro ⟨φ₀, ε, K, hε, hK, hpatch⟩
  obtain ⟨l, hl⟩ := section_support_inFree p hp M hM hb K hK
  obtain ⟨L, hL, hdom⟩ := summable_global_domination p l
  apply (positive_patches_net p f hf.1 (fun i => hf.2.1 (Set.mem_range_self i))).mp hf
  refine ⟨φ₀.comp M.subtypeL, ε, L, hε, hL, ?_⟩
  rintro _ ⟨i, rfl⟩ ψ hψ
  have hmem : ψ - φ₀.comp M.subtypeL ∈
      closure ((fun φ : Dual E => φ.comp M.subtypeL) '' {φ | support K φ < 1}) := by
    rw [restriction_polar M hM K (summable_disk_compact p K hK).1
      (summable_disk_compact p K hK).2.1 (summable_disk_compact p K hK).2.2]
    exact ((show support {x : M | (x : E) ∈ K} (ψ - φ₀.comp M.subtypeL) ≤
      |l (ψ - φ₀.comp M.subtypeL)| by rw [← hl]; exact le_abs_self _).trans
        (hdom _)).trans hψ.le
  have hclosed : IsClosed {θ : Dual M | ε ≤ f i (θ + φ₀.comp M.subtypeL)} :=
    isClosed_le continuous_const
      ((free_function_norm_continuous p (f i)).comp (continuous_id.add continuous_const))
  have hbound : ∀ θ ∈ (fun φ : Dual E => φ.comp M.subtypeL) '' {φ | support K φ < 1},
      ε ≤ f i (θ + φ₀.comp M.subtypeL) := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hh := hpatch _ (Set.mem_range_self i) (φ + φ₀)
      (by simpa only [Set.mem_ofPred_eq, add_sub_cancel_right] using hφ)
    change ε ≤ f i ((φ + φ₀).comp M.subtypeL) at hh
    simpa only [ContinuousLinearMap.add_comp] using hh
  have hh : ε ≤ f i ((ψ - φ₀.comp M.subtypeL) + φ₀.comp M.subtypeL) :=
    (closure_minimal hbound hclosed) hmem
  simpa only [sub_add_cancel] using hh

private theorem finiteSupport_nonneg (A : Finset E) : 0 ≤ finiteSupport A := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨a, ha⟩ := hA
    exact (abs_nonneg (FVLv.of a)).trans (by
      simpa only [finiteSupport, dite_eq_left (show A.Nonempty from ⟨a, ha⟩)] using
        Finset.le_sup' (fun a : E => |FVLv.of a|) ha)
  · simp [finiteSupport, hA]

private theorem finiteSupport_generator_bound (p : Exponent) (M : Submodule ℝ E)
    (A : Finset M) (a : M) (ha : a ∈ A) :
    ‖a‖ ≤ ‖induced p M.subtypeL (ofFVL p (finiteSupport A))‖ := by
  classical
  have hA : A.Nonempty := ⟨a, ha⟩
  have hle : |FVLv.of a| ≤ finiteSupport A := by
    simpa only [finiteSupport, dite_eq_left hA] using Finset.le_sup' (fun x : M => |FVLv.of x|) ha
  have hfree : |delta p a| ≤ ofFVL p (finiteSupport A) := by
    simpa only [VecLatHom.map_abs, ofFVL_of] using (ofFVL p).monotone hle
  have himage : |induced p M.subtypeL (delta p a)| ≤
      induced p M.subtypeL (ofFVL p (finiteSupport A)) := by
    change |(induced p M.subtypeL).toVecLatHom (delta p a)| ≤
      (induced p M.subtypeL).toVecLatHom (ofFVL p (finiteSupport A))
    rw [← VecLatHom.map_abs]
    exact (induced p M.subtypeL).toVecLatHom.monotone hfree
  have hn := norm_le_norm_of_abs_le_abs (himage.trans (le_abs_self _))
  rw [(induced_norm_generators p M.subtypeL).2, (delta p).norm_map] at hn
  exact hn

private theorem finiteSupport_compact_disk [CompleteSpace E] (p : Exponent)
    (M : Submodule ℝ E) (hM : IsClosed (M : Set E)) (A : Finset M) (hA : A.Nonempty) :
    ∃ K : Set M, K.Nonempty ∧ AbsConvex ℝ K ∧ IsCompact K ∧
      (∀ ψ, support K ψ = fvlFunction (finiteSupport A) ψ) ∧
      ∀ x ∈ K, ‖x‖ ≤ ‖induced p M.subtypeL (ofFVL p (finiteSupport A))‖ := by
  let : CompleteSpace M := hM.isComplete.completeSpace_coe
  have hhull := compact_support_closedAbsConvexHull (A : Set M) hA.to_set A.finite_toSet.isCompact
  obtain ⟨hne, hac, hc⟩ := (isPCompactDisk_infinity_iff _).mp hhull.1
  refine ⟨closedAbsConvexHull ℝ (A : Set M), hne, hac, hc,
    fun ψ => (hhull.2 ψ).trans (finiteSupport_support A hA ψ).symm, ?_⟩
  have hsub : (A : Set M) ⊆ Metric.closedBall 0
      ‖induced p M.subtypeL (ofFVL p (finiteSupport A))‖ := by
    intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      finiteSupport_generator_bound p M A x hx
  simpa only [Set.subset_def, Metric.mem_closedBall, dist_zero_right] using
    closedAbsConvexHull_min hsub
      ⟨balanced_closedBall_zero, convex_closedBall (0 : M) _⟩ Metric.isClosed_closedBall

private theorem fvl_norm_separation (p : Exponent) (T : F →L[ℝ] E)
    (hb : ¬ BoundedBelow (induced p T)) (a b : ℝ) (ha : 0 < a) (hbpos : 0 < b) :
    ∃ v : FVL F, ‖ofFVL p v‖ = a ∧ ‖induced p T (ofFVL p v)‖ < b := by
  have hbad : ∃ v : FVL F, ‖induced p T (ofFVL p v)‖ < (b / a) * ‖ofFVL p v‖ := by
    by_contra! h
    exact hb ⟨b / a, div_pos hbpos ha, fun f =>
      (denseRange_ofFVL p).induction_on f
        (isClosed_le (continuous_const.mul continuous_norm)
          (induced p T).toContinuousLinearMap.continuous.norm) h⟩
  obtain ⟨v, hv⟩ := hbad
  have hvpos : 0 < ‖ofFVL p v‖ :=
    (mul_pos_iff_of_pos_left (div_pos hbpos ha)).mp ((norm_nonneg _).trans_lt hv)
  refine ⟨(a / ‖ofFVL p v‖) • v, ?_, ?_⟩
  · rw [map_smul, norm_smul, Real.norm_of_nonneg (div_pos ha hvpos).le]
    exact div_mul_cancel₀ a hvpos.ne'
  · rw [map_smul, map_smul, norm_smul, Real.norm_of_nonneg (div_pos ha hvpos).le]
    have h := mul_lt_mul_of_pos_left hv (div_pos ha hvpos)
    calc
      _ < (a / ‖ofFVL p v‖) * ((b / a) * ‖ofFVL p v‖) := h
      _ = b := by field_simp

private theorem finiteSupport_norm_separation [CompleteSpace E] (p : Exponent)
    (hp : p.IsFinite) (M : Submodule ℝ E) (hM : IsClosed (M : Set E))
    (hb : ¬ BoundedBelow (induced p M.subtypeL)) (a b : ℝ) (ha : 0 < a) (hbpos : 0 < b) :
    ∃ A : Finset M, A.Nonempty ∧ a ≤ ‖ofFVL p (finiteSupport A)‖ ∧
      ‖induced p M.subtypeL (ofFVL p (finiteSupport A))‖ < b := by
  obtain ⟨v, hv, hsmall⟩ := fvl_norm_separation p M.subtypeL hb a (b / 2) ha (half_pos hbpos)
  obtain ⟨A, hA, hnorm⟩ := finite_support_majorant p hp M hM v (b / 2) (half_pos hbpos)
  have hmajor : ‖ofFVL p v‖ ≤ ‖ofFVL p (finiteSupport A)‖ :=
    norm_le_norm_of_abs_le_abs ((free_le_iff p _ _).mpr fun ψ => (hA ψ).trans (le_abs_self _))
  refine ⟨A, ?_, hv ▸ hmajor, by linarith⟩
  by_contra hne
  have hz : finiteSupport A = 0 := by simp [finiteSupport, hne]
  rw [hz, map_zero, norm_zero, hv] at hmajor
  exact ha.not_ge hmajor

private theorem ofFVL_positive_difference (p : Exponent) (e : E) (q : FVL E) :
    ofFVL p ((|FVLv.of e| - q) ⊔ 0) = (|delta p e| - ofFVL p q) ⊔ 0 := by
  simp only [SupHomClass.map_sup, map_sub, VecLatHom.map_abs, ofFVL_of, map_zero]

private theorem induced_positive_difference (p : Exponent) (M : Submodule ℝ E)
    (e : M) (q : FVL M) :
    induced p M.subtypeL (ofFVL p ((|FVLv.of e| - q) ⊔ 0)) =
      (|delta p (e : E)| - induced p M.subtypeL (ofFVL p q)) ⊔ 0 := by
  rw [ofFVL_positive_difference]
  change (induced p M.subtypeL).toVecLatHom _ = _
  simp only [SupHomClass.map_sup, map_sub, VecLatHom.map_abs, map_zero]
  rw [show (induced p M.subtypeL).toVecLatHom (delta p e) = delta p (e : E) from
    (induced_norm_generators p M.subtypeL).2 e]
  rfl

private theorem positive_difference_pos {X : Type*} [NormedAddCommGroup X]
    [Lattice X] [IsOrderedAddMonoid X] [NormedVectorLattice X]
    (x Q : X) (h : ‖Q‖ < ‖x‖) : 0 < (|x| - Q) ⊔ 0 := by
  apply lt_iff_le_not_ge.mpr
  refine ⟨le_sup_right, fun hG => ?_⟩
  have hle : |x| ≤ Q := sub_nonpos.mp (sup_le_iff.mp hG).1
  have hn := norm_le_norm_of_abs_le_abs (hle.trans (le_abs_self Q))
  exact h.not_ge hn

private theorem compact_support_algebraic_order_null [CompleteSpace E] (p : Exponent)
    (hp : p.IsFinite) (K : Set E) (hne : K.Nonempty) (hac : AbsConvex ℝ K)
    (hc : IsCompact K) (hinf : freeNormExt p (support K) = ⊤) (q : ℕ → FVL E)
    (hq : ∀ n, 0 ≤ q n) (hmono : Monotone (fun n => ofFVL p (q n)))
    (hpoint : ∀ ψ, IsLUB (Set.range fun n => fvlFunction (q n) ψ) (support K ψ))
    (e : E) : DecreasesToZero (fun n => ofFVL p ((|FVLv.of e| - q n) ⊔ 0)) := by
  have hpos (n : ℕ) : (0 : Free p E) ≤ ofFVL p (q n) := (ofFVL p).map_nonneg (hq n)
  have hpoint' (ψ : Dual E) :
      IsLUB (Set.range fun n => ofFVL p (q n) ψ) (support K ψ) := by
    simpa only [(model_evaluation p (0 : E) _ _).2] using hpoint ψ
  have hnull := compact_support_order_null p hp K hne hac hc hinf
    (fun n => ofFVL p (q n)) hpos hmono hpoint' e
  simpa only [ofFVL_positive_difference] using hnull

private theorem failure_witness_of_compact_support [CompleteSpace E] (p : Exponent)
    (hp : p.IsFinite) (M : Submodule ℝ E) (hM : IsClosed (M : Set E))
    (K : Set M) (hne : K.Nonempty) (hac : AbsConvex ℝ K) (hc : IsCompact K)
    (hinf : freeNormExt p (support K) = ⊤) (q : ℕ → FVL M)
    (hq : ∀ n, 0 ≤ q n) (hmono : Monotone (fun n => ofFVL p (q n)))
    (hpoint : ∀ ψ, IsLUB (Set.range fun n => fvlFunction (q n) ψ) (support K ψ))
    (Q : Free p E) (hlim : Tendsto (fun n => induced p M.subtypeL (ofFVL p (q n))) atTop (𝓝 Q))
    (hupper : ∀ n, induced p M.subtypeL (ofFVL p (q n)) ≤ Q)
    (e : M) (he : ‖Q‖ < ‖e‖) : FVLFailureWitness p p (induced p M.subtypeL) := by
  let : CompleteSpace M := hM.isComplete.completeSpace_coe
  let f (n : ℕ) : FVL M := (|FVLv.of e| - q n) ⊔ 0
  let G : Free p E := (|delta p (e : E)| - Q) ⊔ 0
  have himage (n : ℕ) : induced p M.subtypeL (ofFVL p (f n)) =
      (|delta p (e : E)| - induced p M.subtypeL (ofFVL p (q n))) ⊔ 0 :=
    induced_positive_difference p M e (q n)
  refine ⟨f, fun _ => le_sup_right, ?_, G, ?_, ?_, ?_⟩
  · exact compact_support_algebraic_order_null p hp K hne hac hc hinf q hq hmono hpoint e
  · apply positive_difference_pos
    simpa only [(delta p).norm_map, Submodule.norm_coe] using he
  · simp_rw [himage]
    exact (tendsto_const_nhds.sub hlim).sup_nhds tendsto_const_nhds
  · intro n
    rw [himage]
    exact sup_le_sup (sub_le_sub_left (hupper n) _) le_rfl

/-- Proposition 4.12 (`prop:poe-necessity`): failure of a lower norm bound produces
an explicit positive algebraic sequence decreasing to zero whose images converge in
norm to a strictly positive lower bound. Thus the inclusion fails even sequential
order continuity. The full witness is recorded by `FVLFailureWitness`. -/
theorem poe_necessity [CompleteSpace E] (p : Exponent) (hp : p.IsFinite)
    (M : Submodule ℝ E) (hM : IsClosed (M : Set E))
    (hb : ¬ BoundedBelow (induced p M.subtypeL)) :
    FVLFailureWitness p p (induced p M.subtypeL) ∧
      ¬ SigmaOrderContinuous (induced p M.subtypeL) := by
  classical
  let : CompleteSpace M := hM.isComplete.completeSpace_coe
  choose A hA hlarge hsmall using fun n : ℕ =>
    finiteSupport_norm_separation p hp M hM hb (n + 1) ((1 / 2 : ℝ) ^ n)
      (by positivity) (by positivity)
  choose K hne hac hc hsupport hbound using fun n =>
    finiteSupport_compact_disk p M hM (A n) (hA n)
  have hbound' (n : ℕ) (x : M) (hx : x ∈ K n) : ‖x‖ ≤ (1 / 2 : ℝ) ^ n :=
    (hbound n x hx).trans (hsmall n).le
  obtain ⟨hDne, hDac, hDc, hDsupport⟩ := seriesDisk_properties K
    (fun n => (1 / 2 : ℝ) ^ n) (fun _ => by positivity) summable_geometric_two
    (fun n => ⟨hne n, hac n, hc n⟩) hbound'
  have hspos (ψ : Dual M) (n : ℕ) : 0 ≤ support (K n) ψ :=
    apply_nonneg (supportSeminorm _ (hne n) (hc n).isBounded) ψ
  have hsum (ψ : Dual M) : Summable (fun n => support (K n) ψ) := by
    apply Summable.of_nonneg_of_le (hspos ψ) _ (summable_geometric_two.mul_left ‖ψ‖)
    intro n
    apply csSup_le ((hne n).image _)
    rintro _ ⟨x, hx, rfl⟩
    exact (ψ.le_opNorm x).trans
      (mul_le_mul_of_nonneg_left (hbound' n x hx) (norm_nonneg _))
  have hinf : freeNormExt p (support (seriesDisk K)) = ⊤ := by
    by_contra hfin
    obtain ⟨n, hn⟩ := exists_nat_gt (freeNormExt p (support (seriesDisk K))).toReal
    have hnorm : freeNormExt p (ofFVL p (finiteSupport (A n))) ≤
        freeNormExt p (support (seriesDisk K)) := by
      apply freeNormExt_mono_abs
      intro ψ
      rw [(model_evaluation p (0 : M) _ _).2, ← hsupport, hDsupport,
        abs_of_nonneg (hspos ψ n), abs_of_nonneg (tsum_nonneg (hspos ψ))]
      exact (hsum ψ).le_tsum n (fun j _ => hspos ψ j)
    rw [freeNormExt_eq_norm] at hnorm
    have h := ENNReal.toReal_mono hfin hnorm
    rw [ENNReal.toReal_ofReal (norm_nonneg _)] at h
    have := hlarge n
    linarith
  let q (n : ℕ) : FVL M := ∑ k ∈ Finset.range n, finiteSupport (A k)
  have hq (n : ℕ) : 0 ≤ q n :=
    Finset.sum_nonneg (fun k _ => finiteSupport_nonneg (A k))
  have hqmono : Monotone (fun n => ofFVL p (q n)) := by
    apply (ofFVL p).monotone.comp
    apply monotone_nat_of_le_succ
    intro n
    simpa only [q, Finset.sum_range_succ, le_add_iff_nonneg_right] using
      finiteSupport_nonneg (A n)
  have hqeval (n : ℕ) (ψ : Dual M) :
      fvlFunction (q n) ψ = ∑ k ∈ Finset.range n, support (K k) ψ := by
    rw [← (model_evaluation p (0 : M) (q n) ψ).2]
    simp only [q, map_sum]
    let ev : Free p M →ₗ[ℝ] ℝ :=
      { toFun := fun f => f ψ
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (map_sum ev _ _).trans
      (Finset.sum_congr rfl fun k _ => (hsupport k ψ).symm)
  have hpoint (ψ : Dual M) :
      IsLUB (Set.range fun n => fvlFunction (q n) ψ) (support (seriesDisk K) ψ) := by
    simp_rw [hqeval, hDsupport]
    apply isLUB_of_tendsto_atTop _ (hsum ψ).hasSum.tendsto_sum_nat
    exact monotone_nat_of_le_succ fun n => by
      simpa only [Finset.sum_range_succ, le_add_iff_nonneg_right] using hspos ψ n
  let r (n : ℕ) := induced p M.subtypeL (ofFVL p (finiteSupport (A n)))
  have hrsum : Summable r :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => (hsmall n).le) summable_geometric_two)
  have hrpos (n : ℕ) : 0 ≤ r n :=
    (induced p M.subtypeL).toVecLatHom.map_nonneg
      ((ofFVL p).map_nonneg (finiteSupport_nonneg (A n)))
  have hqimage (n : ℕ) :
      induced p M.subtypeL (ofFVL p (q n)) = ∑ k ∈ Finset.range n, r k := by
    simp only [q, r, map_sum]
  have hlim : Tendsto (fun n => induced p M.subtypeL (ofFVL p (q n))) atTop (𝓝 (∑' n, r n)) := by
    simpa only [hqimage] using hrsum.hasSum.tendsto_sum_nat
  have hupper (n : ℕ) : induced p M.subtypeL (ofFVL p (q n)) ≤ ∑' k, r k := by
    rw [hqimage]
    exact hrsum.sum_le_tsum _ (fun k _ => hrpos k)
  have : Nontrivial M := by
    by_contra h
    have : Subsingleton M := not_nontrivial_iff_subsingleton.mp h
    have hz : support (seriesDisk K) = (fun _ : Dual M => 0) := by
      funext ψ
      have himage : (fun x : M => |ψ x|) '' seriesDisk K = {0} := by
        ext t
        constructor
        · rintro ⟨x, _, rfl⟩
          simp [Subsingleton.elim x 0]
        · rintro rfl
          exact ⟨0, hDac.1.zero_mem hDne, by simp⟩
      simp only [support, himage, csSup_singleton]
    rw [hz, freeNormExt_zero] at hinf
    exact ENNReal.zero_ne_top hinf
  obtain ⟨e, he⟩ := exists_norm_eq M (c := ‖∑' n, r n‖ + 1) (by positivity)
  have hw := failure_witness_of_compact_support p hp M hM (seriesDisk K) hDne hDac hDc
    hinf q hq hqmono hpoint (∑' n, r n) hlim hupper e (by rw [he]; linarith)
  refine ⟨hw, ?_⟩
  intro hsigma
  obtain ⟨f, _, hf, G, hG, _, hGlower⟩ := hw
  exact hG.not_ge ((hsigma _ hf).2.2 (by rintro _ ⟨n, rfl⟩; exact hGlower n))

/-- Theorem 4.1 (`thm:poe-inclusion`): for finite p and a closed subspace M, order
continuity, sequential order continuity, a lower free-norm bound, and POE-p are
equivalent. Failure of POE-p additionally yields the explicit decreasing-sequence
witness `FVLFailureWitness`. -/
theorem poe_inclusion [CompleteSpace E] (p : Exponent) (hp : p.IsFinite)
    (M : Submodule ℝ E) (hM : IsClosed (M : Set E)) :
    List.TFAE [
      IsOrderContinuousOp (induced p M.subtypeL).toContinuousLinearMap.toLinearMap,
      SigmaOrderContinuous (induced p M.subtypeL),
      BoundedBelow (induced p M.subtypeL), HasPOE p E M] ∧
    (¬ HasPOE p E M → FVLFailureWitness p p (induced p M.subtypeL)) := by
  constructor
  · tfae_have 1 → 2 := orderContinuous_sigmaOrderContinuous
      (induced p M.subtypeL).toContinuousLinearMap.toLinearMap
      (fun _ h => (induced p M.subtypeL).toVecLatHom.map_nonneg h)
    tfae_have 2 → 3 := fun h => by
      by_contra hb
      exact (poe_necessity p hp M hM hb).2 h
    tfae_have 3 → 1 := poe_sufficiency p hp M hM
    tfae_have 4 ↔ 3 := poe_iff_boundedBelow p M hM
    tfae_finish
  · intro h
    exact (poe_necessity p hp M hM (fun hb => h ((poe_iff_boundedBelow p M hM).mpr hb))).1

/-- The regularity/closedness reformulation announced at the start of Section 4. -/
theorem regular_range_iff_closed [CompleteSpace E] (p : Exponent) (hp : p.IsFinite)
    (M : Submodule ℝ E) (hM : IsClosed (M : Set E)) :
    IsRegularSublattice (inducedRange p M.subtypeL) ↔
      IsClosed (inducedRange p M.subtypeL : Set (Free p E)) := by
  classical
  let : CompleteSpace M := hM.isComplete.completeSpace_coe
  let J := induced p M.subtypeL
  have hJ : Function.Injective J :=
    (induced_basic_properties p M.subtypeL).2.1.mpr Subtype.val_injective
  let e : Free p M ≃o inducedRange p M.subtypeL :=
    OrderIso.ofSurjective
      { toFun := fun f => ⟨J f, ⟨f, rfl⟩⟩
        inj' := fun _ _ h => hJ (congrArg Subtype.val h)
        map_rel_iff' := ⟨J.toVecLatHom.le_of_map_le hJ, fun h => J.toVecLatHom.monotone h⟩ }
      (by rintro ⟨_, f, rfl⟩; exact ⟨f, rfl⟩)
  have hezero : e 0 = 0 := Subtype.ext (map_zero J.toContinuousLinearMap)
  have hinvzero : e.symm 0 = 0 := by rw [← hezero, e.symm_apply_apply]
  have hreg : IsRegularSublattice (inducedRange p M.subtypeL) ↔
      IsOrderContinuousOp J.toContinuousLinearMap.toLinearMap := by
    rw [IsRegularSublattice, orderContinuous_iff_decreasing _ (fun _ h => h),
      orderContinuous_iff_decreasing J.toContinuousLinearMap.toLinearMap
        (fun _ h => J.toVecLatHom.map_nonneg h)]
    constructor
    · intro h ι _ _ _ f hf
      apply h ι (fun i => e (f i))
      refine ⟨e.monotone.comp_antitone hf.1, ?_⟩
      rw [Set.range_comp', e.isGLB_image, hinvzero]
      exact hf.2
    · intro h ι _ _ _ f hf
      have hh := h ι (fun i => e.symm (f i))
        ⟨e.symm.monotone.comp_antitone hf.1, by
          rw [Set.range_comp', e.symm.isGLB_image, OrderIso.symm_symm, hezero]; exact hf.2⟩
      have he (x : inducedRange p M.subtypeL) : J (e.symm x) = x :=
        congrArg Subtype.val (e.apply_symm_apply x)
      change DecreasesToZero (fun i => J (e.symm (f i))) at hh
      have heq : (fun i => J (e.symm (f i))) =
          (fun i => (inducedRange p M.subtypeL).subtype.toLinearMap (f i)) :=
        funext fun i => he (f i)
      rw [heq] at hh
      exact hh
  rw [hreg]
  constructor
  · intro h
    have hbb : BoundedBelow J := by
      by_contra hb
      exact (poe_necessity p hp M hM hb).2
        (orderContinuous_sigmaOrderContinuous J.toContinuousLinearMap.toLinearMap
          (fun _ h => J.toVecLatHom.map_nonneg h) h)
    exact ((embedding_iff J.toContinuousLinearMap).mp hbb).2
  · intro hclosed
    exact poe_sufficiency p hp M hM
      ((embedding_iff J.toContinuousLinearMap).mpr ⟨hJ, hclosed⟩)

private theorem decreasesToZero_map_bijective {X : Type u} {Y : Type v}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (S : VecLatHom X Y) (hS : Function.Bijective S) (f : ℕ → X)
    (hf : DecreasesToZero f) : DecreasesToZero (fun n => S (f n)) := by
  refine ⟨S.monotone.comp_antitone hf.1, ⟨?_, ?_⟩⟩
  · rintro _ ⟨n, rfl⟩
    exact S.map_nonneg (hf.2.1 (Set.mem_range_self n))
  · intro b hb
    obtain ⟨a, rfl⟩ := hS.2 b
    have ha : a ≤ 0 := hf.2.2 (by
      rintro _ ⟨n, rfl⟩
      exact S.le_of_map_le hS.1 (hb (Set.mem_range_self n)))
    simpa only [map_zero] using S.monotone ha

private theorem induced_range_reduction [CompleteSpace E] [CompleteSpace F]
    (p : Exponent) (T : F →L[ℝ] E) (hT : BoundedBelow T) :
    (BoundedBelow (induced p T) ↔ BoundedBelow (induced p T.range.subtypeL)) ∧
    (IsOrderContinuousOp (induced p T).toContinuousLinearMap.toLinearMap ↔
      IsOrderContinuousOp (induced p T.range.subtypeL).toContinuousLinearMap.toLinearMap) := by
  classical
  obtain ⟨hTi, hTc⟩ := (embedding_iff T).mp hT
  let : CompleteSpace T.range := hTc.isComplete.completeSpace_coe
  let U := induced p T.rangeRestrict
  have hUi : Function.Injective U :=
    induced_injective_of p T.rangeRestrict (fun _ _ h => hTi (congrArg Subtype.val h))
  have hUs : Function.Surjective U :=
    induced_surjective_of p T.rangeRestrict (by rintro ⟨_, x, rfl⟩; exact ⟨x, rfl⟩)
  let e : Free p F ≃o Free p T.range :=
    OrderIso.ofSurjective
      { toFun := U
        inj' := hUi
        map_rel_iff' := ⟨U.toVecLatHom.le_of_map_le hUi, fun h => U.toVecLatHom.monotone h⟩ } hUs
  have hzero : e 0 = 0 := map_zero U.toContinuousLinearMap
  have hinvzero : e.symm 0 = 0 := by rw [← hzero, e.symm_apply_apply]
  have hfactor (f : Free p F) :
      induced p T.range.subtypeL (U f) = induced p T f := by
    have h := induced_comp p T.range.subtypeL T.rangeRestrict
    exact (congrArg (fun L : Free p F →L[ℝ] Free p E => L f) h).symm
  have hJi : Function.Injective (induced p T) := induced_injective_of p T hTi
  have hIi : Function.Injective (induced p T.range.subtypeL) :=
    induced_injective_of p T.range.subtypeL Subtype.val_injective
  constructor
  · rw [embedding_iff, embedding_iff]
    have hrange : Set.range (induced p T) = Set.range (induced p T.range.subtypeL) := by
      rw [← hUs.range_comp (induced p T.range.subtypeL)]
      congr 1
    simp only [hJi, hIi, true_and, hrange]
  · rw [sigma_order_continuity p (induced p T).toContinuousLinearMap.toLinearMap
      (fun _ h => (induced p T).toVecLatHom.map_nonneg h),
      sigma_order_continuity p (induced p T.range.subtypeL).toContinuousLinearMap.toLinearMap
      (fun _ h => (induced p T.range.subtypeL).toVecLatHom.map_nonneg h)]
    constructor
    · intro h f hf
      have hnull : DecreasesToZero (fun n => e.symm (f n)) := by
        refine ⟨e.symm.monotone.comp_antitone hf.1, ?_⟩
        rw [Set.range_comp', e.symm.isGLB_image, OrderIso.symm_symm, hzero]
        exact hf.2
      have hh := h _ hnull
      have heq : (fun n => induced p T (e.symm (f n))) =
          (fun n => induced p T.range.subtypeL (f n)) := by
        funext n
        rw [← hfactor]
        change induced p T.range.subtypeL (e (e.symm (f n))) = _
        rw [e.apply_symm_apply]
      change DecreasesToZero (fun n => induced p T (e.symm (f n))) at hh
      rw [heq] at hh
      exact hh
    · intro h f hf
      have hh := h _ (decreasesToZero_map_bijective U.toVecLatHom ⟨hUi, hUs⟩ f hf)
      change DecreasesToZero (fun n => induced p T.range.subtypeL (U (f n))) at hh
      simp_rw [hfactor] at hh
      exact hh

private theorem induced_boundedBelow_imp (p : Exponent) (T : F →L[ℝ] E)
    (h : BoundedBelow (induced p T)) : BoundedBelow T := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c, hc, fun x => ?_⟩
  simpa only [(delta p).norm_map, (induced_norm_generators p T).2] using h (delta p x)

private theorem latticeEmbedding_of_boundedBelow (p : Exponent) (T : F →L[ℝ] E)
    (h : BoundedBelow (induced p T)) : IsLatticeEmbedding (induced p T) := by
  have hi := ((embedding_iff (induced p T).toContinuousLinearMap).mp h).1
  exact ⟨h, hi, fun _ _ =>
    ⟨(induced p T).toVecLatHom.le_of_map_le hi, fun h => (induced p T).toVecLatHom.monotone h⟩⟩

private theorem induced_orderContinuous_of_boundedBelow [CompleteSpace E] [CompleteSpace F]
    (p : Exponent) (hp : p.IsFinite) (T : F →L[ℝ] E)
    (h : BoundedBelow (induced p T)) :
    IsOrderContinuousOp (induced p T).toContinuousLinearMap.toLinearMap := by
  have hT := induced_boundedBelow_imp p T h
  have hclosed := ((embedding_iff T).mp hT).2
  have hinc : IsOrderContinuousOp
      (induced p T.range.subtypeL).toContinuousLinearMap.toLinearMap :=
    poe_sufficiency p hp T.range hclosed ((induced_range_reduction p T hT).1.mp h)
  apply (induced_range_reduction p T hT).2.mpr
  exact hinc

private theorem induced_zero_orderContinuous (p : Exponent) (T : F →L[ℝ] E) (hT : T = 0) :
    IsOrderContinuousOp (induced p T).toContinuousLinearMap.toLinearMap := by
  have hz := (induced_eq_zero_iff p T).mpr hT
  intro ι _ _ _ x a _
  change OrderConvergesTo
    (fun i => (induced p T).toContinuousLinearMap (x i)) ((induced p T).toContinuousLinearMap a)
  simpa only [hz, zero_apply] using
    (orderConvergesTo_const (ι := ι) (0 : Free p E))

/-- Section 1's cited characterization of isomorphic lattice embeddings. -/
theorem induced_embedding_iff [CompleteSpace E] [CompleteSpace F]
    (p : Exponent) (T : F →L[ℝ] E) :
    IsLatticeEmbedding (induced p T) ↔ BoundedBelow T ∧ HasPOE p E T.toLinearMap.range := by
  constructor
  · intro h
    have hT := induced_boundedBelow_imp p T h.1
    exact ⟨hT, (poe_iff_boundedBelow p T.range ((embedding_iff T).mp hT).2).mpr
      ((induced_range_reduction p T hT).1.mp h.1)⟩
  · rintro ⟨hT, hpoe⟩
    exact latticeEmbedding_of_boundedBelow p T ((induced_range_reduction p T hT).1.mpr
      ((poe_iff_boundedBelow p T.range ((embedding_iff T).mp hT).2).mp hpoe))

/-- Theorem 1.3 (`thm:intro-poe`): for finite p, an induced map is order continuous
exactly when the original operator is zero or is bounded below with a range having POE.
Equivalently, the induced map itself is zero or an isomorphic lattice embedding.
The proof factors the original operator through its closed range. -/
theorem intro_poe [CompleteSpace E] [CompleteSpace F]
    (p : Exponent) (hp : p.IsFinite) (T : F →L[ℝ] E) :
    (IsOrderContinuousOp (induced p T).toContinuousLinearMap.toLinearMap ↔
      T = 0 ∨ (BoundedBelow T ∧ HasPOE p E T.toLinearMap.range)) ∧
    (IsOrderContinuousOp (induced p T).toContinuousLinearMap.toLinearMap ↔
      (induced p T).toContinuousLinearMap = 0 ∨ IsLatticeEmbedding (induced p T)) := by
  have hfirst : IsOrderContinuousOp (induced p T).toContinuousLinearMap.toLinearMap ↔
      T = 0 ∨ (BoundedBelow T ∧ HasPOE p E T.toLinearMap.range) := by
    constructor
    · intro h
      rcases necessary p T h with hz | hT
      · exact Or.inl hz
      · right
        have hc := ((embedding_iff T).mp hT).2
        have hinc : IsOrderContinuousOp
            (induced p T.range.subtypeL).toContinuousLinearMap.toLinearMap := by
          apply (induced_range_reduction p T hT).2.mp
          exact h
        have hbb : BoundedBelow (induced p T.range.subtypeL) := by
          by_contra hb
          exact (poe_necessity p hp T.range hc hb).2
            (orderContinuous_sigmaOrderContinuous
              (induced p T.range.subtypeL).toContinuousLinearMap.toLinearMap
              (fun _ h => (induced p T.range.subtypeL).toVecLatHom.map_nonneg h) hinc)
        exact ⟨hT, (poe_iff_boundedBelow p T.range hc).mpr hbb⟩
    · rintro (hz | h)
      · exact induced_zero_orderContinuous p T hz
      · exact induced_orderContinuous_of_boundedBelow p hp T
          ((induced_embedding_iff p T).mpr h).1
  refine ⟨hfirst, ?_⟩
  rw [hfirst, induced_eq_zero_iff, induced_embedding_iff]

/-- For every exponent, including ∞, the induced map is order continuous exactly
when the original operator is zero or bounded below with a range having POE. This
combines the finite-parameter theorem with the endpoint criterion `intro_infty`. -/
theorem all_parameter_characterization [CompleteSpace E] [CompleteSpace F]
    (p : Exponent) (T : F →L[ℝ] E) :
    IsOrderContinuousOp (induced p T).toContinuousLinearMap.toLinearMap ↔
      T = 0 ∨ (BoundedBelow T ∧ HasPOE p E T.toLinearMap.range) := by
  rcases lt_or_eq_of_le (le_top : p.1 ≤ ⊤) with hp | hp
  · exact (intro_poe p hp T).1
  · have heq : p = Exponent.infinity := Subtype.ext hp
    subst p
    rw [intro_infty]
    constructor
    · rintro (hz | hT)
      · exact Or.inl hz
      · exact Or.inr ⟨hT, 1, poe_infinity_one T.range ((embedding_iff T).mp hT).2⟩
    · rintro (hz | ⟨hT, _⟩)
      · exact Or.inl hz
      · exact Or.inr hT

/-- An inclusion of a closed complemented subspace induces an order-continuous map
at every exponent: a bounded projection supplies the operator-extension property.
This is the assertion cited in Sections 1–3 as OikhbergEtAl2026, Theorem 3.4. -/
theorem complemented_orderContinuous [CompleteSpace E] (p : Exponent)
    (M : Submodule ℝ E) (hM : M.ClosedComplemented) :
    IsOrderContinuousOp (induced p M.subtypeL).toContinuousLinearMap.toLinearMap := by
  let : CompleteSpace M := hM.isClosed.isComplete.completeSpace_coe
  obtain ⟨P, hP⟩ := hM
  have hcomp : P.comp M.subtypeL = ContinuousLinearMap.id ℝ M :=
    ContinuousLinearMap.ext hP
  have hleft : Function.LeftInverse (induced p P) (induced p M.subtypeL) := by
    intro f
    have hh := induced_comp p P M.subtypeL
    rw [hcomp, induced_id] at hh
    exact (congrArg (fun L : Free p M →L[ℝ] Free p M => L f) hh).symm
  rcases lt_or_eq_of_le (le_top : p.1 ≤ ⊤) with hp | hp
  · apply poe_sufficiency p hp M (show M.ClosedComplemented from ⟨P, hP⟩).isClosed
    apply (embedding_iff (induced p M.subtypeL).toContinuousLinearMap).mpr
    exact ⟨hleft.injective,
      ((induced p M.subtypeL).toContinuousLinearMap.closedComplemented_range_of_leftInverse
        (induced p P).toContinuousLinearMap hleft).isClosed⟩
  · have heq : p = Exponent.infinity :=
      Subtype.ext hp
    subst p
    apply (intro_infty M.subtypeL).mpr
    exact Or.inr ⟨1, zero_lt_one, fun x => by simp⟩

/-- Local complementation by uniformly bounded retractions on finite-dimensional subspaces. -/
def IsLocallyComplemented (M : Submodule ℝ E) : Prop :=
  IsClosed (M : Set E) ∧ ∃ C : ℝ, 1 ≤ C ∧
    ∀ V : Submodule ℝ E, FiniteDimensional ℝ V →
      ∃ P : V →L[ℝ] M, ‖P‖ ≤ C ∧ ∀ x : V, (x : E) ∈ M → (P x : E) = x

/-- Uniformly bounded retractions on finite-dimensional subspaces yield POE by
taking a limit of local extensions. The statement retains the finite-exponent
hypothesis from Section 4.4; the construction itself works for the finite-dimensional
target at every exponent. -/
theorem locallyComplemented_poe (p : Exponent) (_hp : p.IsFinite)
    (M : Submodule ℝ E) (hM : IsLocallyComplemented M) : HasPOE p E M := by
  classical
  obtain ⟨hclosed, C, hC, hlocal⟩ := hM
  refine ⟨C, hclosed, hC, fun n R => ?_⟩
  let V (A : Finset E) := Submodule.span ℝ (A : Set E)
  choose P hP hfix using fun A : Finset E =>
    hlocal (V A) (FiniteDimensional.span_of_finite ℝ A.finite_toSet)
  let s (A : Finset E) (x : E) : FiniteLp p n :=
    if hx : x ∈ V A then R (P A ⟨x, hx⟩) else 0
  have hs (A : Finset E) (x : E) : ‖s A x‖ ≤ C * ‖R‖ * ‖x‖ := by
    dsimp [s]
    split_ifs with hx
    · have h := (R.le_opNorm (P A ⟨x, hx⟩)).trans
        (mul_le_mul_of_nonneg_left ((P A).le_opNorm ⟨x, hx⟩) (norm_nonneg R))
      have h' := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hP A) (norm_nonneg x)) (norm_nonneg R)
      change ‖R (P A ⟨x, hx⟩)‖ ≤ ‖R‖ * (‖P A‖ * ‖x‖) at h
      exact h.trans (by simpa only [mul_left_comm, mul_assoc] using h')
    · simp only [norm_zero]
      exact mul_nonneg (mul_nonneg (zero_le_one.trans hC) (norm_nonneg R)) (norm_nonneg x)
  let B (x : E) := Metric.closedBall (0 : FiniteLp p n) (C * ‖R‖ * ‖x‖)
  let (x : E) : CompactSpace (B x) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let z (A : Finset E) : ∀ x : E, B x :=
    fun x => ⟨s A x, by simpa only [B, Metric.mem_closedBall, dist_zero_right] using hs A x⟩
  let U : Ultrafilter (Finset E) := Ultrafilter.of atTop
  let g : ∀ x : E, B x := (U.map z).lim
  have hg : Tendsto z (U : Filter (Finset E)) (𝓝 g) := (U.map z).le_nhds_lim
  have hpoint (x : E) : Tendsto (fun A => s A x) (U : Filter (Finset E)) (𝓝 (g x : FiniteLp p n)) :=
    continuous_subtype_val.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp hg) x)
  have hmem (x : E) : ∀ᶠ A in (U : Filter (Finset E)), x ∈ V A := by
    apply Filter.Eventually.filter_mono (Ultrafilter.of_le atTop)
    filter_upwards [eventually_ge_atTop ({x} : Finset E)] with A hA
    exact Submodule.subset_span (hA (Finset.mem_singleton_self x))
  have hadd (x y : E) : (g (x + y) : FiniteLp p n) = g x + g y := by
    have heq : ∀ᶠ A in (U : Filter (Finset E)), s A (x + y) = s A x + s A y := by
      filter_upwards [hmem x, hmem y] with A hx hy
      simp only [s, dite_eq_left hx, dite_eq_left hy, dite_eq_left ((V A).add_mem hx hy)]
      change R (P A (⟨x, hx⟩ + ⟨y, hy⟩)) = _
      simp only [map_add]
    exact tendsto_nhds_unique ((hpoint (x + y)).congr' heq) ((hpoint x).add (hpoint y))
  have hsmul (a : ℝ) (x : E) : (g (a • x) : FiniteLp p n) = a • (g x : FiniteLp p n) := by
    have heq : ∀ᶠ A in (U : Filter (Finset E)), s A (a • x) = a • s A x := by
      filter_upwards [hmem x] with A hx
      simp only [s, dite_eq_left hx, dite_eq_left ((V A).smul_mem a hx)]
      change R (P A (a • ⟨x, hx⟩)) = _
      simp only [map_smul]
    exact tendsto_nhds_unique ((hpoint (a • x)).congr' heq) ((hpoint x).const_smul a)
  let L : E →ₗ[ℝ] FiniteLp p n :=
    { toFun := fun x => g x
      map_add' := hadd
      map_smul' := hsmul }
  have hL (x : E) : ‖L x‖ ≤ C * ‖R‖ * ‖x‖ :=
    (mem_closedBall_zero_iff).mp (g x).2
  let S := L.mkContinuous (C * ‖R‖) hL
  refine ⟨S, ?_, L.mkContinuous_norm_le (mul_nonneg (zero_le_one.trans hC) (norm_nonneg R)) hL⟩
  apply ContinuousLinearMap.ext
  intro x
  have heq : ∀ᶠ A in (U : Filter (Finset E)), s A (x : E) = R x := by
    filter_upwards [hmem (x : E)] with A hx
    simp only [s, dite_eq_left hx]
    exact congrArg R (Subtype.ext (hfix A ⟨x, hx⟩ x.2))
  exact tendsto_nhds_unique ((hpoint (x : E)).congr' heq) tendsto_const_nhds

/-- Section 4.4: order continuity for locally complemented subspaces. -/
theorem locallyComplemented_orderContinuous [CompleteSpace E] (p : Exponent)
    (M : Submodule ℝ E) (hM : IsLocallyComplemented M) :
    IsOrderContinuousOp (induced p M.subtypeL).toContinuousLinearMap.toLinearMap := by
  rcases lt_or_eq_of_le (le_top : p.1 ≤ ⊤) with hp | hp
  · exact poe_sufficiency p hp M hM.1
      (boundedBelow_of_poe p M (locallyComplemented_poe p hp M hM))
  · have heq : p = Exponent.infinity := Subtype.ext hp
    subst p
    let : CompleteSpace M := hM.1.isComplete.completeSpace_coe
    apply (intro_infty M.subtypeL).mpr
    exact Or.inr ⟨1, zero_lt_one, fun x => by simp⟩

private theorem continuousMap_approximate_retraction
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (T : C(K, ℝ) →L[ℝ] E) (φ : K → Dual E) (D : ℝ) (hD : 0 ≤ D)
    (hφ : ∀ x, ‖φ x‖ ≤ D) (heval : ∀ f x, φ x (T f) = f x)
    (A : Finset C(K, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : E →L[ℝ] C(K, ℝ), ‖P‖ ≤ D ∧ ∀ f ∈ A, ‖P (T f) - f‖ ≤ ε := by
  classical
  let U (x : K) : Set K := ⋂ f ∈ A, {y | dist (f y) (f x) < ε}
  have ho (x : K) : IsOpen (U x) :=
    isOpen_biInter_finset fun f _ => isOpen_lt (f.continuous.dist continuous_const) continuous_const
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U ho (by
    intro x _
    refine Set.mem_iUnion.mpr ⟨x, ?_⟩
    simp only [U, Set.mem_iInter, Set.mem_ofPred_eq, dist_self]
    exact fun _ _ => hε)
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite
    isClosed_univ (fun i : t => U i) (fun i => ho i) (locallyFinite_of_finite _) (by
      intro y hy
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (ht hy)
      obtain ⟨hxt, hxy⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hxt⟩, hxy⟩)
  have hsum (y : K) : ∑ i : t, ρ i y = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ y)
  let P : E →L[ℝ] C(K, ℝ) := ∑ i : t, (φ i).smulRight (ρ i)
  have hPval (z : E) (y : K) : P z y = ∑ i : t, ρ i y * φ i z := by
    simp [P, mul_comm]
  refine ⟨P, ?_, ?_⟩
  · apply P.opNorm_le_bound hD
    intro z
    apply ((P z).norm_le (mul_nonneg hD (norm_nonneg z))).mpr
    intro y
    rw [Real.norm_eq_abs, hPval]
    calc
      |∑ i : t, ρ i y * φ i z| ≤ ∑ i : t, |ρ i y * φ i z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : t, ρ i y * (D * ‖z‖) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (ρ.nonneg i y)]
        exact mul_le_mul_of_nonneg_left
          (((φ i).le_opNorm z).trans (mul_le_mul_of_nonneg_right (hφ i) (norm_nonneg z)))
          (ρ.nonneg i y)
      _ = D * ‖z‖ := by rw [← Finset.sum_mul, hsum, one_mul]
  · intro f hf
    apply ((P (T f) - f).norm_le hε.le).mpr
    intro y
    have heq : (P (T f) - f) y = ∑ i : t, ρ i y * (f i - f y) := by
      simp only [ContinuousMap.sub_apply, hPval, heval]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
    rw [Real.norm_eq_abs, heq]
    calc
      |∑ i : t, ρ i y * (f i - f y)| ≤ ∑ i : t, |ρ i y * (f i - f y)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : t, ρ i y * ε := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (ρ.nonneg i y)]
        by_cases hi : ρ i y = 0
        · simp only [hi, zero_mul, le_refl]
        · have hy : y ∈ U i := hρ i (subset_tsupport (ρ i) hi)
          have hd : dist (f y) (f i) < ε := Set.mem_iInter.mp (Set.mem_iInter.mp hy f) hf
          apply mul_le_mul_of_nonneg_left _ (ρ.nonneg i y)
          simpa only [Real.dist_eq, abs_sub_comm] using hd.le
      _ = ε := by rw [← Finset.sum_mul, hsum, one_mul]

private theorem induced_isometry_of_dual_extension (p : Exponent) (T : F →L[ℝ] E)
    (hT : ‖T‖ ≤ 1) (Φ : Dual F →ₗᵢ[ℝ] Dual E)
    (hext : ∀ ψ, (Φ ψ).comp T = ψ) : Isometry (induced p T) := by
  apply AddMonoidHomClass.isometry_of_norm (induced p T).toContinuousLinearMap
  intro f
  apply le_antisymm
  · exact ((induced p T).toContinuousLinearMap.le_opNorm f).trans (by
      rw [(induced_norm_generators p T).1]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hT (norm_nonneg f))
  · apply (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).mp
    rw [← freeNormExt_eq_norm p f, ← freeNormExt_eq_norm p (induced p T f)]
    by_cases htop : p.1 = ⊤
    · simp only [freeNormExt, ite_eq_left htop]
      refine iSup_le fun ψ => iSup_le fun hψ => ?_
      exact le_iSup_of_le (Φ ψ) (le_iSup_of_le (by simpa only [Φ.norm_map] using hψ)
        (by rw [canonical_map_formulas, hext]))
    · simp only [freeNormExt, ite_eq_right htop]
      refine iSup_le fun n => iSup_le fun ψ => iSup_le fun hψ => ?_
      exact le_iSup_of_le n (le_iSup_of_le (fun i => Φ (ψ i))
        (le_iSup_of_le (normAdmissible_linearIsometry p Φ ψ hψ)
          (by simp only [canonical_map_formulas, hext]; exact le_rfl)))

/-- Corollary 4.13 (`cor:bidual-order-continuity`): the canonical isometric embedding
of a Banach space into its bidual induces an order-continuous isometric lattice
embedding at every exponent. The canonical embedding of the dual into its bidual
extends dual functionals isometrically; this gives the free-norm bound and hence
order continuity. -/
theorem bidual_order_continuity [CompleteSpace E] (p : Exponent) :
    IsOrderContinuousOp (induced (F := E) (E := Dual (Dual E)) p
      (NormedSpace.inclusionInDoubleDual ℝ E)).toContinuousLinearMap.toLinearMap ∧
    Isometry (induced (F := E) (E := Dual (Dual E)) p (NormedSpace.inclusionInDoubleDual ℝ E)) ∧
    IsLatticeEmbedding (induced (F := E) (E := Dual (Dual E)) p
      (NormedSpace.inclusionInDoubleDual ℝ E)) := by
  let T : E →L[ℝ] Dual (Dual E) := NormedSpace.inclusionInDoubleDual ℝ E
  have hiso : Isometry (induced p T) := by
    apply induced_isometry_of_dual_extension (E := Dual (Dual E)) (F := E)
      p T (NormedSpace.inclusionInDoubleDual_norm_le ℝ E)
      (NormedSpace.inclusionInDoubleDualLi (E := Dual E) ℝ)
    intro ψ
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have hbb : BoundedBelow (induced p T) :=
    ⟨1, zero_lt_one, fun f => by
      simpa only [one_mul] using (hiso.norm_map_of_map_zero
        (map_zero (induced p T).toContinuousLinearMap) f).ge⟩
  refine ⟨?_, hiso, latticeEmbedding_of_boundedBelow p T hbb⟩
  rcases lt_or_eq_of_le (le_top : p.1 ≤ ⊤) with hp | hp
  · exact induced_orderContinuous_of_boundedBelow p hp T hbb
  · have heq : p = Exponent.infinity := Subtype.ext hp
    subst p
    apply (intro_infty T).mpr
    exact Or.inr (induced_boundedBelow_imp Exponent.infinity T hbb)

private theorem finiteLp_extension_of_dual_extension (p : Exponent)
    (T : F →L[ℝ] E) (Φ : Dual F →ₗᵢ[ℝ] Dual E) (hext : ∀ ψ, (Φ ψ).comp T = ψ)
    (n : ℕ) (R : F →L[ℝ] FiniteLp p n) :
    ∃ S : E →L[ℝ] FiniteLp p n, S.comp T = R ∧ ‖S‖ ≤ ‖R‖ := by
  let ψ (i : Fin n) : Dual F := (PiLp.proj p.1 (fun _ : Fin n => ℝ) i).comp R
  let S : E →L[ℝ] FiniteLp p n :=
    (PiLp.continuousLinearEquiv p.1 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun i => Φ (ψ i)))
  refine ⟨S, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    apply WithLp.ofLp_injective p.1
    funext i
    exact congrArg (fun l : Dual F => l x) (hext (ψ i))
  · apply S.opNorm_le_bound (norm_nonneg R)
    intro x
    obtain ⟨l, hl, hlx⟩ := exists_dual_vector'' ℝ (S x)
    change l (S x) = ‖S x‖ at hlx
    let a (i : Fin n) : ℝ := l (PiLp.single p.1 i 1)
    have hlin (z : FiniteLp p n) : ∑ i, a i * z i = l z := by
      have hz := (PiLp.basisFun p.1 ℝ (Fin n)).sum_repr z
      simpa [a, map_sum, map_smul, smul_eq_mul, mul_comm] using congrArg l hz
    let θ : Dual F := ∑ i, a i • ψ i
    have hθ : ‖θ‖ ≤ ‖R‖ := by
      apply θ.opNorm_le_bound (norm_nonneg R)
      intro y
      change ‖(∑ i, a i • ψ i) y‖ ≤ ‖R‖ * ‖y‖
      simp only [sum_apply, smul_apply, smul_eq_mul]
      change ‖∑ i, a i * (R y) i‖ ≤ _
      rw [hlin]
      exact (l.le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right hl (norm_nonneg _)).trans (by
          simpa only [one_mul] using R.le_opNorm y))
    have heval : Φ θ x = l (S x) := by
      simp only [θ, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
      exact hlin (S x)
    have hh := (Φ θ).le_opNorm x
    rw [heval, hlx, Real.norm_of_nonneg (norm_nonneg _), Φ.norm_map] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hθ (norm_nonneg _))

/-- The canonical copy of a Banach space in its bidual has POE with constant one
at every exponent. This follows from the isometric free-lattice inclusion and
`poe_one_iff_isometry`. -/
theorem bidual_poe_one [CompleteSpace E] (p : Exponent) :
    POEWith p (Dual (Dual E)) (NormedSpace.inclusionInDoubleDual ℝ E).toLinearMap.range 1 := by
  let T : E →L[ℝ] Dual (Dual E) := NormedSpace.inclusionInDoubleDual ℝ E
  have hclosed := Isometry.isClosedEmbedding (f := T)
    (NormedSpace.inclusionInDoubleDualLi (E := E) ℝ).isometry
  refine ⟨hclosed.isClosed_range, le_rfl, fun n R => ?_⟩
  obtain ⟨S, hS, hnorm⟩ := finiteLp_extension_of_dual_extension p T
    (NormedSpace.inclusionInDoubleDualLi (E := Dual E) ℝ)
    (fun ψ => ContinuousLinearMap.ext (fun _ => rfl)) n (R.comp T.rangeRestrict)
  refine ⟨S, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    rintro ⟨_, x, rfl⟩
    exact congrArg (fun L : E →L[ℝ] FiniteLp p n => L x) hS
  · rw [one_mul]
    apply hnorm.trans
    apply (R.comp T.rangeRestrict).opNorm_le_bound (norm_nonneg R)
    intro x
    exact (R.le_opNorm (T.rangeRestrict x)).trans
      (mul_le_mul_of_nonneg_left (NormedSpace.double_dual_bound ℝ E x) (norm_nonneg R))

private theorem finiteLp_extension_of_approximations {ι : Type w}
    (p : Exponent) (n : ℕ) (l : Filter ι) [l.NeBot]
    (T : F →L[ℝ] E) (R : F →L[ℝ] FiniteLp p n) (C : ℝ) (hC : 0 ≤ C)
    (S : ι → E →L[ℝ] FiniteLp p n) (hS : ∀ k, ‖S k‖ ≤ C)
    (hlim : ∀ x, Tendsto (fun k => S k (T x)) l (𝓝 (R x))) :
    ∃ A : E →L[ℝ] FiniteLp p n, A.comp T = R ∧ ‖A‖ ≤ C := by
  let B (x : E) := Metric.closedBall (0 : FiniteLp p n) (C * ‖x‖)
  let (x : E) : CompactSpace (B x) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let z (k : ι) : ∀ x : E, B x := fun x => ⟨S k x, by
    apply mem_closedBall_zero_iff.mpr
    exact ((S k).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hS k) (norm_nonneg x))⟩
  let U : Ultrafilter ι := Ultrafilter.of l
  let g : ∀ x : E, B x := (U.map z).lim
  have hg : Tendsto z (U : Filter ι) (𝓝 g) := (U.map z).le_nhds_lim
  have hpoint (x : E) : Tendsto (fun k => S k x) (U : Filter ι) (𝓝 (g x : FiniteLp p n)) :=
    continuous_subtype_val.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp hg) x)
  let L : E →ₗ[ℝ] FiniteLp p n :=
    { toFun := fun x => g x
      map_add' := fun x y => tendsto_nhds_unique
        ((hpoint (x + y)).congr' (Filter.Eventually.of_forall fun k => map_add (S k) x y))
        ((hpoint x).add (hpoint y))
      map_smul' := fun a x => tendsto_nhds_unique
        ((hpoint (a • x)).congr' (Filter.Eventually.of_forall fun k => map_smul (S k) a x))
        ((hpoint x).const_smul a) }
  have hL (x : E) : ‖L x‖ ≤ C * ‖x‖ := mem_closedBall_zero_iff.mp (g x).2
  refine ⟨L.mkContinuous C hL, ?_, L.mkContinuous_norm_le hC hL⟩
  apply ContinuousLinearMap.ext
  intro x
  exact tendsto_nhds_unique (hpoint (T x)) ((hlim x).mono_left (Ultrafilter.of_le l))

private theorem continuousMap_extension_data [CompleteSpace E]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (T : C(K, ℝ) →L[ℝ] E) (hT : BoundedBelow T) :
    ∃ D : ℝ, 0 < D ∧ ∃ φ : K → Dual E,
      (∀ x, ‖φ x‖ ≤ D) ∧ ∀ f x, φ x (T f) = f x := by
  obtain ⟨hi, hc⟩ := (embedding_iff T).mp hT
  obtain ⟨c, hcpos, hbound⟩ := hT
  let e := T.equivRange hi hc
  have hinv (y : T.range) : ‖e.symm y‖ ≤ c⁻¹ * ‖y‖ := by
    obtain ⟨y, f, rfl⟩ := y
    change ‖e.symm ⟨T f, ⟨f, rfl⟩⟩‖ ≤ c⁻¹ * ‖T f‖
    rw [show e.symm ⟨T f, ⟨f, rfl⟩⟩ = f from T.equivRange_symm_apply hi hc f]
    have hh := mul_le_mul_of_nonneg_left (hbound f) (inv_nonneg.mpr hcpos.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hcpos.ne', one_mul] using hh
  let ψ (x : K) : Dual T.range := (ContinuousMap.evalCLM ℝ x).comp e.symm.toContinuousLinearMap
  have hψ (x : K) : ‖ψ x‖ ≤ c⁻¹ := by
    apply (ψ x).opNorm_le_bound (inv_nonneg.mpr hcpos.le)
    intro y
    exact ((e.symm y).norm_coe_le_norm x).trans (hinv y)
  choose φ hφ hnorm using fun x => exists_extension_norm_eq T.range (ψ x)
  refine ⟨c⁻¹, inv_pos.mpr hcpos, φ, fun x => (hnorm x).trans_le (hψ x), ?_⟩
  intro f x
  rw [hφ x ⟨T f, ⟨f, rfl⟩⟩]
  change e.symm ⟨T f, ⟨f, rfl⟩⟩ x = f x
  rw [show e.symm ⟨T f, ⟨f, rfl⟩⟩ = f from T.equivRange_symm_apply hi hc f]

/-- Section 4.4: any embedding of a C(K) space has order-continuous extension. -/
theorem continuousMap_embedding_orderContinuous [CompleteSpace E] (p : Exponent)
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (T : C(K, ℝ) →L[ℝ] E) (hT : BoundedBelow T) :
    IsOrderContinuousOp (induced p T).toContinuousLinearMap.toLinearMap := by
  classical
  obtain ⟨D, hD, φ, hφ, heval⟩ := continuousMap_extension_data T hT
  choose P hP happrox using fun (A : Finset C(K, ℝ)) (k : ℕ) =>
    continuousMap_approximate_retraction T φ D hD.le hφ heval A (1 / (k + 1)) (by positivity)
  have hlim (f : C(K, ℝ)) :
      Tendsto (fun i : Finset C(K, ℝ) × ℕ => P i.1 i.2 (T f)) atTop (𝓝 f) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    have hsmall : 1 / ((N : ℝ) + 1) < ε := by
      rw [div_lt_iff₀ (by positivity)]
      have hh := (div_lt_iff₀ hε).mp hN
      nlinarith
    refine ⟨({f}, N), fun i hi => ?_⟩
    rw [dist_eq_norm]
    apply (happrox i.1 i.2 f (hi.1 (Finset.mem_singleton_self f))).trans_lt
    apply lt_of_le_of_lt _ hsmall
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hi.2 1
  have hpoe : HasPOE p E T.range := by
    let C := max 1 (D * ‖T‖)
    refine ⟨C, ((embedding_iff T).mp hT).2, le_max_left _ _, fun n R => ?_⟩
    let R' : C(K, ℝ) →L[ℝ] FiniteLp p n := R.comp T.rangeRestrict
    have hR' : ‖R'‖ ≤ ‖R‖ * ‖T‖ := by
      apply R'.opNorm_le_bound (mul_nonneg (norm_nonneg R) (norm_nonneg T))
      intro x
      exact (R.le_opNorm (T.rangeRestrict x)).trans (by
        change ‖R‖ * ‖T x‖ ≤ (‖R‖ * ‖T‖) * ‖x‖
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg R))
    let S (i : Finset C(K, ℝ) × ℕ) : E →L[ℝ] FiniteLp p n := R'.comp (P i.1 i.2)
    have hS (i : Finset C(K, ℝ) × ℕ) : ‖S i‖ ≤ C * ‖R‖ := by
      calc
        ‖S i‖ ≤ ‖R'‖ * ‖P i.1 i.2‖ := R'.opNorm_comp_le _
        _ ≤ (‖R‖ * ‖T‖) * D :=
          mul_le_mul hR' (hP i.1 i.2) (norm_nonneg (P i.1 i.2))
            (mul_nonneg (norm_nonneg R) (norm_nonneg T))
        _ = (D * ‖T‖) * ‖R‖ := by ring
        _ ≤ C * ‖R‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg R)
    obtain ⟨B, hB, hBnorm⟩ := finiteLp_extension_of_approximations p n atTop T R'
      (C * ‖R‖) (mul_nonneg (zero_le_one.trans (le_max_left _ _)) (norm_nonneg R))
      S hS (fun f => (R'.continuous.tendsto f).comp (hlim f))
    refine ⟨B, ?_, hBnorm⟩
    apply ContinuousLinearMap.ext
    rintro ⟨_, f, rfl⟩
    exact congrArg (fun L : C(K, ℝ) →L[ℝ] FiniteLp p n => L f) hB
  rcases lt_or_eq_of_le (le_top : p.1 ≤ ⊤) with hp | hp
  · apply induced_orderContinuous_of_boundedBelow p hp T
    exact (induced_range_reduction p T hT).1.mpr (boundedBelow_of_poe p T.range hpoe)
  · have heq : p = Exponent.infinity := Subtype.ext hp
    subst p
    apply (intro_infty T).mpr
    exact Or.inr hT

/-- The real Banach space c0 of null sequences, realized as continuous functions on the
discrete natural numbers that vanish at infinity, with the supremum norm. -/
abbrev CZero := ZeroAtInftyContinuousMap ℕ ℝ
/-- The real Banach space of bounded sequences, modeled by Mathlib’s `lp` at exponent ∞. -/
abbrev LInfinity : Type := lp (fun _ : ℕ => ℝ) ⊤

/-- The canonical bounded linear inclusion of real null sequences into bounded sequences.
It preserves each coordinate; `c0_isometry_uncomplemented` proves that it is isometric
and that its range is not complemented. -/
def c0Inclusion : CZero →L[ℝ] LInfinity := by
  let L : CZero →ₗ[ℝ] LInfinity :=
    { toFun := fun f => ⟨fun n => f n, memℓp_infty
        ⟨‖f‖, by
          rintro _ ⟨n, rfl⟩
          exact f.toBCF.norm_coe_le_norm n⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact L.mkContinuous 1 fun f => by
    rw [one_mul]
    exact lp.norm_le_of_forall_le (norm_nonneg f) (fun n => f.toBCF.norm_coe_le_norm n)

private theorem c0Inclusion_isometry : Isometry c0Inclusion := by
  apply AddMonoidHomClass.isometry_of_norm c0Inclusion
  intro f
  apply le_antisymm
  · exact lp.norm_le_of_forall_le (norm_nonneg f) (fun n => f.toBCF.norm_coe_le_norm n)
  · change ‖f.toBCF‖ ≤ ‖c0Inclusion f‖
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro n
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero (c0Inclusion f) n

private theorem c0Inclusion_boundedBelow : BoundedBelow c0Inclusion :=
  ⟨1, zero_lt_one, fun f => by
    simpa only [one_mul] using
      (c0Inclusion_isometry.norm_map_of_map_zero (map_zero c0Inclusion) f).ge⟩

/-- Truncate a bounded sequence to its first `k` coordinates as an element of `c₀`. -/
def c0Truncation (k : ℕ) : LInfinity →L[ℝ] CZero := by
  let L : LInfinity →ₗ[ℝ] CZero :=
    { toFun := fun x =>
        { toFun := fun i => if i < k then x i else 0
          continuous_toFun := continuous_of_discreteTopology
          zero_at_infty' := by
            rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
            apply tendsto_const_nhds.congr'
            filter_upwards [eventually_ge_atTop k] with i hi
            simp only [ite_eq_right (not_lt.mpr hi)] }
      map_add' := fun x y => by
        ext i
        change (if i < k then x i + y i else 0) =
          (if i < k then x i else 0) + (if i < k then y i else 0)
        split_ifs <;> simp
      map_smul' := fun a x => by
        ext i
        change (if i < k then a • x i else 0) = a • (if i < k then x i else 0)
        split_ifs <;> simp }
  exact L.mkContinuous 1 fun x => by
    rw [one_mul]
    change ‖(L x).toBCF‖ ≤ ‖x‖
    apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
    intro i
    change ‖if i < k then x i else 0‖ ≤ ‖x‖
    split_ifs
    · exact lp.norm_apply_le_norm ENNReal.top_ne_zero x i
    · simpa only [norm_zero] using norm_nonneg x

private theorem c0Truncation_norm_le (k : ℕ) (x : LInfinity) :
    ‖c0Truncation k x‖ ≤ ‖x‖ := by
  change ‖(c0Truncation k x).toBCF‖ ≤ ‖x‖
  apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
  intro i
  change ‖if i < k then x i else 0‖ ≤ ‖x‖
  split_ifs
  · exact lp.norm_apply_le_norm ENNReal.top_ne_zero x i
  · simpa only [norm_zero] using norm_nonneg x

private theorem c0Truncation_tendsto (x : CZero) :
    Tendsto (fun k => c0Truncation k (c0Inclusion x)) atTop (𝓝 x) := by
  have hx : Tendsto x atTop (𝓝 0) := by
    simpa only [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using zero_at_infty x
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hx) (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk => ?_⟩
  apply lt_of_le_of_lt _ (half_lt_self hε)
  rw [dist_eq_norm]
  change ‖(c0Truncation k (c0Inclusion x) - x).toBCF‖ ≤ ε / 2
  apply (BoundedContinuousFunction.norm_le (half_pos hε).le).mpr
  intro i
  change ‖(if i < k then x i else 0) - x i‖ ≤ ε / 2
  split_ifs with hi
  · simpa only [sub_self, norm_zero] using (half_pos hε).le
  · simpa only [zero_sub, norm_neg, dist_zero_right] using (hN i (hk.trans (not_lt.mp hi))).le

/-- The known POE assertion about the c0 pair, cited before Theorem 1.3. -/
theorem c0_poe (p : Exponent) : HasPOE p LInfinity c0Inclusion.toLinearMap.range := by
  refine ⟨1, ((embedding_iff c0Inclusion).mp c0Inclusion_boundedBelow).2,
    le_rfl, fun n R => ?_⟩
  let R' : CZero →L[ℝ] FiniteLp p n := R.comp c0Inclusion.rangeRestrict
  let S (k : ℕ) : LInfinity →L[ℝ] FiniteLp p n := R'.comp (c0Truncation k)
  have hR (x : CZero) : ‖R' x‖ ≤ ‖R‖ * ‖x‖ := by
    have h := R.le_opNorm (c0Inclusion.rangeRestrict x)
    change ‖R' x‖ ≤ ‖R‖ * ‖c0Inclusion x‖ at h
    rwa [c0Inclusion_isometry.norm_map_of_map_zero (map_zero c0Inclusion)] at h
  have hS (k : ℕ) : ‖S k‖ ≤ ‖R‖ := by
    apply (S k).opNorm_le_bound (norm_nonneg R)
    intro x
    exact (hR (c0Truncation k x)).trans
      (mul_le_mul_of_nonneg_left (c0Truncation_norm_le k x) (norm_nonneg R))
  obtain ⟨A, hA, hAnorm⟩ := finiteLp_extension_of_approximations p n atTop c0Inclusion R'
    ‖R‖ (norm_nonneg R) S hS (fun x =>
      (R'.continuous.tendsto x).comp (c0Truncation_tendsto x))
  refine ⟨A, ?_, by simpa only [one_mul] using hAnorm⟩
  apply ContinuousLinearMap.ext
  rintro ⟨_, x, rfl⟩
  exact congrArg (fun L : CZero →L[ℝ] FiniteLp p n => L x) hA

/-- Corollary 3.3 (`cor:c0`): the canonical inclusion of null sequences into bounded
sequences induces an order-continuous free-lattice map at every exponent. Together
with `c0_isometry_uncomplemented`, this exhibits order continuity for an uncomplemented pair. -/
theorem c0 (p : Exponent) :
    IsOrderContinuousOp (induced p c0Inclusion).toContinuousLinearMap.toLinearMap := by
  rcases lt_or_eq_of_le (le_top : p.1 ≤ ⊤) with hp | hp
  · apply induced_orderContinuous_of_boundedBelow p hp c0Inclusion
    exact (induced_range_reduction p c0Inclusion c0Inclusion_boundedBelow).1.mpr
      (boundedBelow_of_poe p c0Inclusion.range (c0_poe p))
  · have heq : p = Exponent.infinity := Subtype.ext hp
    subst p
    apply (intro_infty c0Inclusion).mpr
    exact Or.inr c0Inclusion_boundedBelow

private theorem c0_annihilator_bound (φ : Dual LInfinity)
    (hφ : ∀ x : CZero, φ (c0Inclusion x) = 0) (x : LInfinity)
    (C : ℝ) (hC : 0 ≤ C) (hx : ∀ᶠ i in atTop, ‖x i‖ ≤ C) :
    ‖φ x‖ ≤ ‖φ‖ * C := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hx
  have hy : ‖x - c0Inclusion (c0Truncation N x)‖ ≤ C := by
    apply lp.norm_le_of_forall_le hC
    intro i
    change ‖x i - (if i < N then x i else 0)‖ ≤ C
    split_ifs with hi
    · simpa only [sub_self, norm_zero] using hC
    · simpa only [sub_zero] using hN i (not_lt.mp hi)
  have h := (φ.le_opNorm (x - c0Inclusion (c0Truncation N x))).trans
    (mul_le_mul_of_nonneg_left hy (norm_nonneg φ))
  simpa only [map_sub, hφ, sub_zero] using h

/-- The bounded zero-one indicator sequence of a set of natural numbers. -/
def boundedIndicator (A : Set ℕ) : LInfinity := by
  classical
  exact ⟨fun i => if i ∈ A then 1 else 0, memℓp_infty ⟨1, by
    rintro _ ⟨i, rfl⟩
    dsimp only
    split_ifs <;> norm_num⟩⟩

private theorem annihilator_countable_support {ι : Type*} (A : ι → Set ℕ)
    (hA : ∀ r s, r ≠ s → (A r ∩ A s).Finite) (φ : Dual LInfinity)
    (hφ : ∀ x : CZero, φ (c0Inclusion x) = 0) :
    (Function.support (fun r => φ (boundedIndicator (A r)))).Countable := by
  classical
  have hs : Summable (fun r => |φ (boundedIndicator (A r))|) := by
    apply summable_of_sum_le (fun _ => abs_nonneg _) (c := ‖φ‖)
    intro t
    let σ (r : ι) : ℝ := if 0 ≤ φ (boundedIndicator (A r)) then 1 else -1
    let x : LInfinity := ∑ r ∈ t, σ r • boundedIndicator (A r)
    have hdis : ∀ᶠ i in atTop, ∀ r ∈ t, ∀ s ∈ t,
        r ≠ s → ¬ (i ∈ A r ∧ i ∈ A s) := by
      simp only [eventually_all_finset]
      intro r hr s hs
      by_cases hrs : r = s
      · simp [hrs]
      · exact ((Nat.cofinite_eq_atTop ▸ (hA r s hrs).eventually_cofinite_notMem)).mono
          (fun _ hi _ => hi)
    have hx : ∀ᶠ i in atTop, ‖x i‖ ≤ 1 := by
      filter_upwards [hdis] with i hi
      change ‖(lp.evalₗ (𝕜 := ℝ) (fun _ : ℕ => ℝ) ⊤ i) x‖ ≤ 1
      simp only [x, map_sum, map_smul, lp.evalₗ_apply]
      by_cases hex : ∃ r ∈ t, i ∈ A r
      · obtain ⟨r, hr, hir⟩ := hex
        rw [Finset.sum_eq_single r (fun s hs hsr => by
          have his : i ∉ A s := fun his => hi s hs r hr hsr ⟨his, hir⟩
          simp [boundedIndicator, his]) (fun hr' => (hr' hr).elim)]
        simp only [boundedIndicator, ite_eq_left hir, smul_eq_mul, mul_one]
        dsimp only [σ]
        split_ifs <;> norm_num
      · have hz (r : ι) (hr : r ∈ t) : i ∉ A r := fun hir => hex ⟨r, hr, hir⟩
        rw [Finset.sum_eq_zero (fun r hr => by simp [boundedIndicator, hz r hr])]
        norm_num
    have heq : φ x = ∑ r ∈ t, |φ (boundedIndicator (A r))| := by
      simp only [x, map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro r hr
      dsimp only [σ]
      split_ifs with hrpos
      · simp [abs_of_nonneg hrpos]
      · simp [abs_of_neg (lt_of_not_ge hrpos)]
    have hb := c0_annihilator_bound φ hφ x 1 zero_le_one hx
    rw [heq, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)),
      mul_one] at hb
    exact hb
  exact hs.countable_support.mono (fun r hr => abs_ne_zero.mpr hr)

/-- Encode the first `n` bits of a Boolean sequence as a natural number. -/
def prefixCode (r : ℕ → Bool) (n : ℕ) : ℕ :=
  Encodable.encode (List.ofFn (fun i : Fin n => r i))

private theorem prefixCode_eq {r s : ℕ → Bool} {n m : ℕ}
    (h : prefixCode r n = prefixCode s m) :
    n = m ∧ ∀ i < n, r i = s i := by
  have hl := Encodable.encode_injective h
  have hn : n = m := by simpa only [List.length_ofFn] using congrArg List.length hl
  subst m
  refine ⟨rfl, ?_⟩
  exact fun i hi => congrFun (List.ofFn_inj.mp hl) ⟨i, hi⟩

/-- Distinct infinite binary branches have only finitely many common prefixes. -/
private theorem prefixCode_finite_inter {r s : ℕ → Bool} (hrs : r ≠ s) :
    (Set.range (prefixCode r) ∩ Set.range (prefixCode s)).Finite := by
  obtain ⟨d, hd⟩ := Function.ne_iff.mp hrs
  apply ((Set.finite_Iic d).image (prefixCode r)).subset
  rintro x ⟨⟨n, rfl⟩, m, hm⟩
  refine ⟨n, ?_, rfl⟩
  exact le_of_not_gt (fun hn => hd ((prefixCode_eq hm.symm).2 d hn))

private theorem binaryBranch_uncountable : Uncountable (ℕ → Bool) := by
  apply uncountable_iff_forall_not_surjective.mpr
  intro f hf
  obtain ⟨n, hn⟩ := hf (fun i => !(f i i))
  have hd := congrFun hn n
  cases h : f n n <;> simp [h] at hd

/-- The uncomplemented-range observation introducing Corollary 3.3. -/
theorem c0_isometry_uncomplemented :
    Isometry c0Inclusion ∧ ¬ c0Inclusion.toLinearMap.range.ClosedComplemented := by
  classical
  refine ⟨c0Inclusion_isometry, ?_⟩
  rintro ⟨P, hP⟩
  let Q : LInfinity →L[ℝ] LInfinity :=
    ContinuousLinearMap.id ℝ LInfinity - c0Inclusion.range.subtypeL.comp P
  have hQ (x : CZero) : Q (c0Inclusion x) = 0 := by
    change c0Inclusion x - (P (c0Inclusion x) : LInfinity) = 0
    exact sub_eq_zero.mpr (congrArg Subtype.val (hP (c0Inclusion.rangeRestrict x))).symm
  let φ (n : ℕ) : Dual LInfinity := (lp.evalCLM ℝ (fun _ : ℕ => ℝ) ⊤ n).comp Q
  let A (r : ℕ → Bool) : Set ℕ := Set.range (prefixCode r)
  have hc : (⋃ n, Function.support (fun r => φ n (boundedIndicator (A r)))).Countable :=
    Set.countable_iUnion (fun n => annihilator_countable_support A
      (fun _ _ hrs => prefixCode_finite_inter hrs) (φ n) (fun x => by
        change (Q (c0Inclusion x)) n = 0
        rw [hQ]
        rfl))
  have hex : ∃ r, r ∉ ⋃ n, Function.support (fun r => φ n (boundedIndicator (A r))) := by
    let := binaryBranch_uncountable
    by_contra hn
    push Not at hn
    exact Set.not_countable_univ ((Set.eq_univ_iff_forall.mpr hn) ▸ hc)
  obtain ⟨r, hr⟩ := hex
  have hz : Q (boundedIndicator (A r)) = 0 := by
    apply lp.ext
    funext n
    exact not_ne_iff.mp (fun hn => hr (Set.mem_iUnion.mpr ⟨n, hn⟩))
  have heq : boundedIndicator (A r) = (P (boundedIndicator (A r)) : LInfinity) :=
    sub_eq_zero.mp hz
  obtain ⟨x, hx⟩ := (P (boundedIndicator (A r))).property
  have hx' : c0Inclusion x = boundedIndicator (A r) := hx.trans heq.symm
  have htail : Tendsto x atTop (𝓝 0) := by
    simpa only [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using zero_at_infty x
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp htail) (1 / 2) (by norm_num)
  have hinf : (A r).Infinite :=
    Set.infinite_range_of_injective (fun _ _ h => (prefixCode_eq h).1)
  obtain ⟨i, hi, hiN⟩ := hinf.exists_notMem_finset (Finset.range N)
  have hsmall := hN i (by simpa only [Finset.mem_range, not_lt] using hiN)
  have hxi : x i = 1 := by
    have hh := congrArg (fun z : LInfinity => z i) hx'
    change x i = (if i ∈ A r then 1 else 0) at hh
    simpa only [ite_eq_left hi] using hh
  norm_num [hxi] at hsmall

/-- Section 3: separable injectivity, with arbitrary closed subspaces of separable superspaces. -/
def SeparablyInjective (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F] : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] (M : Submodule ℝ X), IsClosed (M : Set X) →
    ∀ T : M →L[ℝ] F, ∃ S : X →L[ℝ] F, S.comp M.subtypeL = T

/-- The unnumbered generalization after Corollary 3.3: an isomorphic embedding of a
separable, separably injective Banach space induces an order-continuous map at every
exponent. Separable reduction makes it possible to use injectivity on a separable
ambient subspace even when the original target is not separable. -/
theorem separably_injective_embedding [CompleteSpace E] [CompleteSpace F]
    [TopologicalSpace.SeparableSpace F] (p : Exponent)
    (hF : SeparablyInjective.{u, v} F) (T : F →L[ℝ] E) (hT : BoundedBelow T) :
    IsOrderContinuousOp (induced p T).toContinuousLinearMap.toLinearMap := by
  by_contra hnot
  obtain ⟨M, N, h, hM, hN, hMs, hNs, hMtop, hbad⟩ := separable_reduction p T hnot
  have htop := hMtop inferInstance
  subst M
  let : CompleteSpace (⊤ : Submodule ℝ F) := hM.1.isComplete.completeSpace_coe
  let : CompleteSpace N := hN.1.isComplete.completeSpace_coe
  let : TopologicalSpace.SeparableSpace N := hNs
  let R := restrictOperator T ⊤ N h
  have hR : BoundedBelow R := by
    obtain ⟨c, hc, hbound⟩ := hT
    exact ⟨c, hc, fun x => hbound x⟩
  obtain ⟨hi, hc⟩ := (embedding_iff R).mp hR
  let e := R.equivRange hi hc
  let U : R.range →L[ℝ] F := (⊤ : Submodule ℝ F).subtypeL.comp e.symm.toContinuousLinearMap
  obtain ⟨S, hS⟩ := hF N R.range hc U
  let Q : N →L[ℝ] (⊤ : Submodule ℝ F) :=
    (Submodule.topContEquiv (R := ℝ) (M := F)).symm.toContinuousLinearMap.comp S
  have hleft : Function.LeftInverse Q R := by
    intro x
    apply Subtype.ext
    have hh := congrArg (fun L : R.range →L[ℝ] F => L ⟨R x, ⟨x, rfl⟩⟩) hS
    change S (R x) = (e.symm ⟨R x, ⟨x, rfl⟩⟩ : F) at hh
    change S (R x) = (x : F)
    rw [hh]
    exact congrArg Subtype.val (R.equivRange_symm_apply hi hc x)
  have hcompl := R.closedComplemented_range_of_leftInverse Q hleft
  apply hbad
  apply (induced_range_reduction p R hR).2.mpr
  exact complemented_orderContinuous p R.range hcompl

end FBLOrderContinuousLH
