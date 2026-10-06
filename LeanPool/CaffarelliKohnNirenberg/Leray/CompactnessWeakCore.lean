/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.UniformSpace.CompleteSeparated
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorSupSmoothBoundSupport
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Topology.Bases
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Compactness Weak Core

Supporting estimates for the Navier–Stokes development.
-/

public section

open Filter Set Topology MeasureTheory
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩

@[expose]
def smoothCompactLpSet : Set
    (Lp L2Vec3 (2 : ℝ≥0∞) (volume : Measure Vec3)) :=
  {f | ∃ g : Vec3 → L2Vec3, f =ᵐ[volume] g ∧ HasCompactSupport g ∧
    ContDiff ℝ (⊤ : ℕ∞) g}

private instance : SecondCountableTopology smoothCompactLpSet := inferInstance

private instance : TopologicalSpace.SeparableSpace smoothCompactLpSet :=
  TopologicalSpace.SecondCountableTopology.to_separableSpace

private instance : Nonempty smoothCompactLpSet := by
  refine ⟨⟨0, ?_⟩⟩
  exact ⟨fun _ => 0, by filter_upwards [] with x; simp,
    HasCompactSupport.zero, contDiff_const⟩

private theorem dense_smoothCompactLpSet : Dense smoothCompactLpSet :=
  by
    simpa [smoothCompactLpSet] using
      Lp.dense_hasCompactSupport_contDiff (E := Vec3) (F := L2Vec3)
        (p := (2 : ℝ≥0∞)) (μ := volume) (by norm_num)

/-- A countable family of smooth compactly supported vector fields is dense in
global spatial L². It supplies the test family used for weak slice convergence
in lem:compactness. -/
theorem exists_countable_dense_smooth_compact_vector_tests :
    ∃ ψ : ℕ → Vec3 → L2Vec3,
      (∀ n, HasCompactSupport (ψ n) ∧ ContDiff ℝ (⊤ : ℕ∞) (ψ n)) ∧
      ∃ hψ : ∀ n, MemLp (ψ n) 2 (volume : Measure Vec3),
        DenseRange (fun n => (hψ n).toLp) := by
  classical
  let σ : ℕ → smoothCompactLpSet := TopologicalSpace.denseSeq smoothCompactLpSet
  let ψ : ℕ → Vec3 → L2Vec3 := fun n => Classical.choose (σ n).property
  let hprop : ∀ n, (σ n).val =ᵐ[volume] ψ n ∧
      HasCompactSupport (ψ n) ∧ ContDiff ℝ (⊤ : ℕ∞) (ψ n) := by
    intro n
    exact Classical.choose_spec (σ n).property
  have hreg : ∀ n, HasCompactSupport (ψ n) ∧ ContDiff ℝ (⊤ : ℕ∞) (ψ n) :=
    fun n => (hprop n).2
  let hψ : ∀ n, MemLp (ψ n) 2 (volume : Measure Vec3) := fun n =>
    (hreg n).2.continuous.memLp_of_hasCompactSupport (hreg n).1
  have hclass : ∀ n, (hψ n).toLp = (σ n).val := by
    intro n
    apply Lp.ext
    filter_upwards [(hψ n).coeFn_toLp, (hprop n).1] with x h₁ h₂
    exact h₁.trans h₂.symm
  have hseq : DenseRange σ := TopologicalSpace.denseRange_denseSeq smoothCompactLpSet
  have hdense : Dense smoothCompactLpSet := dense_smoothCompactLpSet
  refine ⟨ψ, hreg, hψ, ?_⟩
  change Dense (range fun n => (hψ n).toLp)
  have hsubset : smoothCompactLpSet ⊆
      closure (range fun n => (hψ n).toLp) := by
    intro x hx
    have hxSubtype : (⟨x, hx⟩ : smoothCompactLpSet) ∈ closure (range σ) := by
      change Dense (range σ) at hseq
      rw [dense_iff_closure_eq] at hseq
      simp [hseq]
    have hxVals := closure_subtype.1 hxSubtype
    have hset : (fun y : smoothCompactLpSet => y.val) '' range σ =
        range (fun n => (σ n).val) := by
      ext y
      simp
    rw [hset] at hxVals
    have heqRange : range (fun n => (σ n).val) =
        range (fun n => (hψ n).toLp) := by
      ext y
      simp only [Set.mem_range]
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨n, hclass n⟩
      · rintro ⟨n, rfl⟩
        exact ⟨n, (hclass n).symm⟩
    rw [heqRange] at hxVals
    exact hxVals
  rw [dense_iff_closure_eq]
  have hdense' : closure smoothCompactLpSet = univ := hdense.closure_eq
  rw [← hdense']
  have hrange : range (fun n => (hψ n).toLp) ⊆ smoothCompactLpSet := by
    rintro y ⟨n, rfl⟩
    refine ⟨ψ n, (hψ n).coeFn_toLp, (hreg n).1, (hreg n).2⟩
  exact le_antisymm (closure_minimal (hrange.trans subset_closure) isClosed_closure)
    (closure_minimal hsubset isClosed_closure)

/-- A countable family of relatively compact scalar sequences has one common
subsequence on which every coordinate converges. This is the diagonal step in
`lem:compactness`. -/
theorem exists_strictMono_tendsto_forall_of_isCompact_closure_range
    {ι : Type*} {β : ι → Type*} [Countable ι]
    [∀ i, TopologicalSpace (β i)] [∀ i, FirstCountableTopology (β i)]
    (f : ℕ → ∀ i, β i)
    (hcompact : ∀ i, IsCompact (closure (range fun n => f n i))) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : ∀ i, β i,
      ∀ i, Tendsto (fun n => f (ψ n) i) atTop (nhds (g i)) := by
  let K : Set (∀ i, β i) := Set.pi univ fun i => closure (range fun n => f n i)
  have hK : IsCompact K := isCompact_univ_pi hcompact
  have hfK : ∀ n, f n ∈ K := by
    intro n i _
    exact subset_closure (mem_range_self n)
  obtain ⟨g, hgK, ψ, hψ, hconv⟩ := hK.tendsto_subseq hfK
  refine ⟨ψ, hψ, g, fun i => ?_⟩
  have hEval : Continuous (fun x : ∀ j, β j => x i) := continuous_apply i
  exact hEval.continuousAt.tendsto.comp hconv

/-- A uniformly equicontinuous family of continuous scalar maps on a compact
space, with pointwise relatively compact values, is relatively compact in the
uniform topology. This supplies the fixed-test time compactness in
`lem:compactness`. -/
theorem isCompact_closure_range_of_equicontinuous
    {X β : Type*} [TopologicalSpace X] [CompactSpace X]
    [CompactlyCoherentSpace X] [UniformSpace β] [T2Space β] [CompleteSpace β]
    (f : ℕ → C(X, β))
    (hequi : EquicontinuousOn (fun g : range f => (g : X → β)) univ)
    (hvalues : ∀ x, ∃ K : Set β, IsCompact K ∧ ∀ n, f n x ∈ K) :
    IsCompact (closure (range f)) := by
  let 𝔖 : Set (Set X) := {K | IsCompact K}
  have hCover : ⋃₀ 𝔖 = univ := by
    ext x
    constructor
    · intro _
      exact mem_univ x
    · intro _
      apply mem_sUnion.mpr
      refine ⟨{x}, ?_, by simp⟩
      exact isCompact_singleton
  have hT2 : T2Space (UniformOnFun X β 𝔖) :=
    UniformOnFun.t2Space_of_covering hCover
  have hT1 : T1Space (UniformOnFun X β 𝔖) :=
    @T2Space.t1Space (UniformOnFun X β 𝔖) _ hT2
  have hT0 : T0Space (UniformOnFun X β 𝔖) :=
    @T1Space.t0Space (UniformOnFun X β 𝔖) _ hT1
  have hF : IsClosedEmbedding
      (UniformOnFun.ofFun 𝔖 ∘ fun g : C(X, β) => (g : X → β)) := by
    have hUniform : IsUniformEmbedding
        (ContinuousMap.toUniformOnFunIsCompact :
          C(X, β) → UniformOnFun X β {K | IsCompact K}) :=
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
    exact @IsUniformEmbedding.isClosedEmbedding
      (C(X, β)) (UniformOnFun X β 𝔖) inferInstance inferInstance inferInstance
      hT0 ContinuousMap.toUniformOnFunIsCompact hUniform
  exact ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (𝔖_compact := by intro K hK; exact hK)
    (F_clemb := hF)
    (s_eqcont := fun K _ => hequi.mono (subset_univ K))
    (s_pointwiseCompact := by
      intro K hK x hx
      obtain ⟨Q, hQ, hQf⟩ := hvalues x
      refine ⟨Q, hQ, ?_⟩
      intro g hg
      rcases hg with ⟨n, rfl⟩
      exact hQf n)

/-- One subsequence makes a countable family of bounded equicontinuous scalar
pairings converge uniformly on their compact time sets. This is the diagonal
extraction in lem:compactness. -/
theorem exists_common_subsequence_uniform_convergence
    {ι : Type*} [Countable ι] {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, CompactlyCoherentSpace (X i)]
    (F : ℕ → ∀ i, C(X i, ℝ))
    (hequi : ∀ i, EquicontinuousOn
      (fun g : range fun n => F n i => (g : X i → ℝ)) univ)
    (hvalues : ∀ i x, ∃ K : Set ℝ, IsCompact K ∧ ∀ n, F n i x ∈ K) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ G : ∀ i, C(X i, ℝ),
      ∀ i, Tendsto (fun n => F (ψ n) i) atTop (nhds (G i)) := by
  have hcompact : ∀ i, IsCompact (closure (range fun n => F n i)) := by
    intro i
    exact isCompact_closure_range_of_equicontinuous
      (fun n => F n i) (hequi i) (hvalues i)
  exact exists_strictMono_tendsto_forall_of_isCompact_closure_range F hcompact

/-- Uniformly bounded linear functionals that converge on a dense sequence
converge pointwise everywhere. The limit is again a continuous linear
functional. This is the extension step in the Riesz representation argument
for lem:compactness. -/
theorem exists_limit_clm_of_tendsto_on_dense_range
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℕ → E →L[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ n, ‖F n‖ ≤ C) (ψ : ℕ → E) (hψ : DenseRange ψ)
    (hconv : ∀ m, ∃ a : ℝ,
      Tendsto (fun n => F n (ψ m)) atTop (nhds a)) :
    ∃ L : E →L[ℝ] ℝ,
      (∀ x, Tendsto (fun n => F n x) atTop (nhds (L x))) ∧
      ∀ x, ‖L x‖ ≤ C * ‖x‖ := by
  have hseq (x : E) : CauchySeq (fun n => F n x) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    let δ : ℝ := ε / (4 * (C + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨m, hxy⟩ := hψ.exists_dist_lt x hδ
    obtain ⟨a, ha⟩ := hconv m
    have haCauchy : CauchySeq (fun n => F n (ψ m)) := ha.cauchySeq
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp haCauchy) (ε / 2)
      (by positivity)
    have hsmall : C * δ ≤ ε / 4 := by
      have hfrac : C / (4 * (C + 1)) ≤ (1 / 4 : ℝ) := by
        apply (div_le_iff₀ (by positivity)).2
        nlinarith only [hC]
      calc
        C * δ = ε * (C / (4 * (C + 1))) := by dsimp [δ]; ring
        _ ≤ ε * (1 / 4) := mul_le_mul_of_nonneg_left hfrac hε.le
        _ = ε / 4 := by ring
    refine ⟨N, fun n hn p hp => ?_⟩
    have hleft : dist (F n x) (F n (ψ m)) ≤ C * δ := by
      calc
        dist (F n x) (F n (ψ m)) = ‖F n x - F n (ψ m)‖ := dist_eq_norm _ _
        _ = ‖F n (x - ψ m)‖ := by rw [map_sub]
        _ ≤ ‖F n‖ * ‖x - ψ m‖ := ContinuousLinearMap.le_opNorm (F n) _
        _ ≤ C * dist x (ψ m) := by
          rw [dist_eq_norm]
          exact mul_le_mul_of_nonneg_right (hF n) (norm_nonneg _)
        _ ≤ C * δ := mul_le_mul_of_nonneg_left hxy.le hC
    have hmiddle : dist (F n (ψ m)) (F p (ψ m)) < ε / 2 := hN n hn p hp
    have hright : dist (F p (ψ m)) (F p x) ≤ C * δ := by
      calc
        dist (F p (ψ m)) (F p x) = ‖F p (ψ m) - F p x‖ := dist_eq_norm _ _
        _ = ‖F p (ψ m - x)‖ := by rw [map_sub]
        _ ≤ ‖F p‖ * ‖ψ m - x‖ := ContinuousLinearMap.le_opNorm (F p) _
        _ ≤ C * dist (ψ m) x := by
          rw [dist_eq_norm]
          exact mul_le_mul_of_nonneg_right (hF p) (norm_nonneg _)
        _ = C * dist x (ψ m) := by rw [dist_comm]
        _ ≤ C * δ := mul_le_mul_of_nonneg_left hxy.le hC
    calc
      dist (F n x) (F p x) ≤
          dist (F n x) (F n (ψ m)) +
            (dist (F n (ψ m)) (F p (ψ m)) + dist (F p (ψ m)) (F p x)) := by
              calc
                dist (F n x) (F p x) ≤
                    dist (F n x) (F n (ψ m)) + dist (F n (ψ m)) (F p x) :=
                  dist_triangle _ _ _
                _ ≤ dist (F n x) (F n (ψ m)) +
                    (dist (F n (ψ m)) (F p (ψ m)) +
                      dist (F p (ψ m)) (F p x)) := by
                    gcongr
                    exact dist_triangle _ _ _
      _ < ε / 4 + (ε / 2 + ε / 4) :=
        add_lt_add_of_le_of_lt (hleft.trans hsmall)
          (add_lt_add_of_lt_of_le hmiddle (hright.trans hsmall))
      _ = ε := by ring
  have hlim (x : E) :
      Tendsto (fun n => F n x) atTop
        (nhds (Filter.atTop.limUnder (fun n => F n x))) :=
    (hseq x).tendsto_limUnder
  let L : E →ₗ[ℝ] ℝ := {
    toFun := fun x => Filter.atTop.limUnder (fun n => F n x)
    map_add' := by
      intro x y
      apply tendsto_nhds_unique (hlim (x + y))
      have hsum := (hlim x).add (hlim y)
      have hsum' : Tendsto (fun n => F n x + F n y) atTop
          (nhds (Filter.atTop.limUnder (fun n => F n x) +
            Filter.atTop.limUnder (fun n => F n y))) := hsum
      have heq : (fun n => F n (x + y)) = (fun n => F n x + F n y) := by
        funext n
        exact map_add (F n) x y
      rw [← heq] at hsum'
      simpa using hsum'
    map_smul' := by
      intro c x
      apply tendsto_nhds_unique (hlim (c • x))
      have hsmul := (hlim x).const_smul c
      have heq : (fun n => F n (c • x)) = fun n => c • F n x := by
        funext n
        exact map_smul (F n) c x
      rw [← heq] at hsmul
      simpa using hsmul }
  have hLbound (x : E) : ‖L x‖ ≤ C * ‖x‖ := by
    apply le_of_tendsto (hlim x).norm
    filter_upwards [] with n
    calc
      ‖F n x‖ ≤ ‖F n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm (F n) x
      _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_right (hF n) (norm_nonneg x)
  let Lc : E →L[ℝ] ℝ := L.mkContinuous C hLbound
  refine ⟨Lc, ?_, hLbound⟩
  intro x
  change Tendsto (fun n => F n x) atTop (nhds (L x))
  exact hlim x

/-- A bounded sequence in a real Hilbert space has a weak limit when its
pairings converge on a dense sequence. This is the slice representation step
in lem:compactness. -/
theorem exists_weak_limit_of_tendsto_pairings_on_dense_range
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (u : ℕ → E) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n, ‖u n‖ ≤ C) (ψ : ℕ → E) (hψ : DenseRange ψ)
    (hpair : ∀ m, ∃ a : ℝ,
      Tendsto (fun n => inner ℝ (u n) (ψ m)) atTop (nhds a)) :
    ∃ v : E, ∀ x, Tendsto (fun n => inner ℝ (u n) x) atTop
      (nhds (inner ℝ v x)) := by
  let F : ℕ → E →L[ℝ] ℝ := fun n => innerSL ℝ (u n)
  have hF : ∀ n, ‖F n‖ ≤ C := by
    intro n
    change ‖innerSL ℝ (u n)‖ ≤ C
    rw [innerSL_apply_norm]
    exact hbound n
  have hconv : ∀ m, ∃ a : ℝ,
      Tendsto (fun n => F n (ψ m)) atTop (nhds a) := by
    intro m
    obtain ⟨a, ha⟩ := hpair m
    refine ⟨a, ?_⟩
    simpa only [F, innerSL_apply_apply] using ha
  obtain ⟨L, hL, _hLbound⟩ :=
    exists_limit_clm_of_tendsto_on_dense_range F C hC hF ψ hψ hconv
  let v : E := (InnerProductSpace.toDual ℝ E).symm L
  refine ⟨v, fun x => ?_⟩
  simpa only [F, innerSL_apply_apply, v,
    InnerProductSpace.toDual_symm_apply] using hL x

end CKN.Leray
