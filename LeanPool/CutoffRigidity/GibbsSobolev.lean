/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.CompactGibbsGenerator

/-!
# The genuine closed weighted Gibbs gradient and energy domain

Compact Gibbs integration by parts proves closability of the actual L²
gradient. Its graph closure defines the weighted H¹ domain and closed energy.
No essential self-adjointness or spectral attainment is asserted.
-/

public section

namespace CutoffRigidity

open MeasureTheory
open scoped LinearPMap ENNReal

/-- An actual energy pairing proves closability: a zero-input graph limit
is orthogonal to, and lies in the closure of, the gradient range. -/
theorem isClosable_of_gradient_energy_pairing
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (G : H →ₗ.[ℝ] K) (A : G.domain → H)
    (henergy : ∀ u v : G.domain, inner ℝ (G u) (G v) = inner ℝ (u : H) (A v)) :
    G.IsClosable := by
  let C := G.graph.topologicalClosure
  have hgraph : ∀ p : H × K, p ∈ C → p.1 = 0 → p.2 = 0 := by
    intro p hp hp0
    have hp' : p ∈ closure (G.graph : Set (H × K)) := hp
    have hpair (v : G.domain) : inner ℝ p.2 (G v) = inner ℝ p.1 (A v) := by
      have hc : IsClosed {q : H × K | inner ℝ q.2 (G v) = inner ℝ q.1 (A v)} :=
        isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)
      apply closure_minimal (t := {q : H × K | inner ℝ q.2 (G v) = inner ℝ q.1 (A v)}) ?_ hc hp'
      intro q hq
      obtain ⟨u, huf, hug⟩ := (G.mem_graph_iff).mp hq
      change inner ℝ q.2 (G v) = inner ℝ q.1 (A v)
      rw [← huf, ← hug]
      exact henergy u v
    have horth (z : K) (hz : z ∈ Set.range G.toFun) : inner ℝ p.2 z = 0 := by
      obtain ⟨v, rfl⟩ := hz
      change inner ℝ p.2 (G v) = 0
      rw [hpair, hp0, inner_zero_left]
    have hrange : p.2 ∈ closure (Set.range G.toFun) := by
      have hc : IsClosed (Prod.snd ⁻¹' closure (Set.range G.toFun) : Set (H × K)) :=
        isClosed_closure.preimage continuous_snd
      apply closure_minimal (t := Prod.snd ⁻¹' closure (Set.range G.toFun)) ?_ hc hp'
      intro q hq
      obtain ⟨u, huf, hug⟩ := (G.mem_graph_iff).mp hq
      apply subset_closure
      exact ⟨u, hug⟩
    have hself : inner ℝ p.2 p.2 = 0 := by
      have hc : IsClosed {z : K | inner ℝ p.2 z = 0} :=
        isClosed_eq (continuous_const.inner continuous_id) continuous_const
      exact closure_minimal (fun z hz => horth z hz) hc hrange
    exact inner_self_eq_zero.mp hself
  refine ⟨C.toLinearPMap, ?_⟩
  exact (Submodule.toLinearPMap_graph_eq C hgraph).symm

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Compact C² functions have actual Gibbs L² gradients. -/
theorem compactGibbsGradient_memLp {V : E → ℝ}
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u : compactGibbsGeneratorDomain V) :
    MemLp (gradient (compactGibbsRepresentative V u)) 2 (gibbsMeasure volume V) := by
  let := hprob
  have hf := (compactGibbsRepresentative_spec V u).1
  have hc := (compactGibbsRepresentative_spec V u).2.1
  have hG : HasCompactSupport (gradient (compactGibbsRepresentative V u)) :=
    (hc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp)
  exact (continuous_gradient_of_c1 (hf.of_le (by norm_num))).memLp_of_hasCompactSupport hG

/-- Actual compact gradients as a linear map between actual Gibbs L² spaces. -/
@[expose] noncomputable def compactGibbsGradientMap {V : E → ℝ} (hV : Continuous V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    compactGibbsGeneratorDomain V →ₗ[ℝ] (E →₂[gibbsMeasure volume V] E) where
  toFun := fun u => (compactGibbsGradient_memLp hprob u).toLp (gradient (compactGibbsRepresentative
    V u))
  map_add' := by
    intro u v
    apply Lp.ext
    filter_upwards [(compactGibbsGradient_memLp hprob (u + v)).coeFn_toLp,
      (compactGibbsGradient_memLp hprob u).coeFn_toLp,
      (compactGibbsGradient_memLp hprob v).coeFn_toLp,
      Lp.coeFn_add ((compactGibbsGradient_memLp hprob u).toLp _)
        ((compactGibbsGradient_memLp hprob v).toLp _)] with x huv hu hv hadd
    rw [huv, hadd, Pi.add_apply, hu, hv]
    have hrep := (compactGibbsRepresentativeLinear V hV).map_add u v
    rw [show compactGibbsRepresentative V (u + v) =
      compactGibbsRepresentative V u + compactGibbsRepresentative V v from hrep]
    change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ
      (compactGibbsRepresentative V u + compactGibbsRepresentative V v) x) = _
    rw [fderiv_add ((compactGibbsRepresentative_spec V u).1.differentiable (by norm_num) x)
      ((compactGibbsRepresentative_spec V v).1.differentiable (by norm_num) x), map_add]
    rfl
  map_smul' := by
    intro r u
    apply Lp.ext
    filter_upwards [(compactGibbsGradient_memLp hprob (r • u)).coeFn_toLp,
      (compactGibbsGradient_memLp hprob u).coeFn_toLp,
      Lp.coeFn_smul r ((compactGibbsGradient_memLp hprob u).toLp _)] with x hru hu hs
    simp only [RingHom.id_apply]
    rw [hru, hs, Pi.smul_apply, hu]
    have hrep := (compactGibbsRepresentativeLinear V hV).map_smul r u
    rw [show compactGibbsRepresentative V (r • u) = r • compactGibbsRepresentative V u from hrep]
    change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (r • compactGibbsRepresentative V u) x) = _
    rw [fderiv_const_smul ((compactGibbsRepresentative_spec V u).1.differentiable (by norm_num) x),
      map_smul]
    rfl

/-- The genuine partially defined Gibbs L² gradient. -/
@[expose] noncomputable def compactGibbsGradient {V : E → ℝ} (hV : Continuous V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    (E →₂[gibbsMeasure volume V] ℝ) →ₗ.[ℝ] (E →₂[gibbsMeasure volume V] E) where
  domain := compactGibbsGeneratorDomain V
  toFun := compactGibbsGradientMap hV hprob

/-- The actual Hilbert gradient energy is given by compact weighted Gibbs IBP. -/
theorem compactGibbsGradient_energy_pairing {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u v : compactGibbsGeneratorDomain V) :
    inner ℝ (compactGibbsGradient hV.continuous hprob u) (compactGibbsGradient hV.continuous hprob
      v) =
      inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) (-compactGibbsGenerator hV hprob v) := by
  rw [inner_neg_right, inner_compactGibbsGenerator,
    gibbs_energy_compact_differentiated_test hV (compactGibbsRepresentative_spec V u).1
      (compactGibbsRepresentative_spec V v).1 (compactGibbsRepresentative_spec V v).2.1, neg_neg,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(compactGibbsGradient_memLp hprob u).coeFn_toLp,
    (compactGibbsGradient_memLp hprob v).coeFn_toLp] with x hu hv
  change inner ℝ ((compactGibbsGradient_memLp hprob u).toLp _ x)
    ((compactGibbsGradient_memLp hprob v).toLp _ x) = _
  rw [hu, hv]

/-- The actual compact Gibbs gradient is closable, with no global assumed
Sobolev regularity or stipulated Dirichlet-form closure. -/
theorem compactGibbsGradient_isClosable {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    (compactGibbsGradient hV.continuous hprob).IsClosable :=
  isClosable_of_gradient_energy_pairing (compactGibbsGradient hV.continuous hprob)
    (fun v => -compactGibbsGenerator hV hprob v) (compactGibbsGradient_energy_pairing hV hprob)

/-- The closed weighted gradient is the actual graph closure. -/
@[expose] noncomputable def closedGibbsGradient {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    (E →₂[gibbsMeasure volume V] ℝ) →ₗ.[ℝ] (E →₂[gibbsMeasure volume V] E) :=
  (compactGibbsGradient hV.continuous hprob).closure

/-- The graph closure is genuinely closed. -/
theorem closedGibbsGradient_isClosed {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    (closedGibbsGradient hV hprob).IsClosed :=
  (compactGibbsGradient_isClosable hV hprob).closure_isClosed

/-- The actual weighted H¹ domain as a subspace of Gibbs L². Its Hilbert
graph topology is constructed below rather than inherited from L². -/
@[expose] noncomputable def gibbsSobolevDomain {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    Submodule ℝ (E →₂[gibbsMeasure volume V] ℝ) :=
  (closedGibbsGradient hV hprob).domain

/-- The closed gradient graph, in the Hilbert L² product norm. This is the
genuine weighted H¹ space, with squared norm L² norm plus gradient energy. -/
@[expose] noncomputable def gibbsSobolevGraph {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    Submodule ℝ (WithLp 2 ((E →₂[gibbsMeasure volume V] ℝ) × (E →₂[gibbsMeasure volume V] E))) :=
  (closedGibbsGradient hV hprob).graph.comap
    (WithLp.linearEquiv 2 ℝ ((E →₂[gibbsMeasure volume V] ℝ) × (E →₂[gibbsMeasure volume V]
      E))).toLinearMap

/-- Closedness is inherited from the proved closed gradient graph through
the actual continuous equivalence of the product norms. -/
theorem gibbsSobolevGraph_isClosed {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    IsClosed (gibbsSobolevGraph hV hprob :
      Set (WithLp 2 ((E →₂[gibbsMeasure volume V] ℝ) × (E →₂[gibbsMeasure volume V] E)))) :=
  (closedGibbsGradient_isClosed hV hprob).preimage
    (WithLp.prodContinuousLinearEquiv 2 ℝ
      (E →₂[gibbsMeasure volume V] ℝ) (E →₂[gibbsMeasure volume V] E)).continuous

/-- Completeness for the genuine graph norm: the Dirichlet energy is closed. -/
noncomputable instance gibbsSobolevGraph_completeSpace {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) : CompleteSpace (gibbsSobolevGraph hV
      hprob) :=
  (gibbsSobolevGraph_isClosed hV hprob).completeSpace_coe

/-- The continuous inclusion of weighted H¹ into the actual Gibbs L² space. -/
@[expose] noncomputable def gibbsSobolevInclusion {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    gibbsSobolevGraph hV hprob →L[ℝ] (E →₂[gibbsMeasure volume V] ℝ) :=
  (ContinuousLinearMap.fst ℝ _ _).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ
      (E →₂[gibbsMeasure volume V] ℝ) (E →₂[gibbsMeasure volume V] E)).toContinuousLinearMap.comp
        (gibbsSobolevGraph hV hprob).subtypeL)

/-- The closed weak gradient, continuous in the graph Hilbert norm. -/
@[expose] noncomputable def gibbsSobolevDerivative {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    gibbsSobolevGraph hV hprob →L[ℝ] (E →₂[gibbsMeasure volume V] E) :=
  (ContinuousLinearMap.snd ℝ _ _).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ
      (E →₂[gibbsMeasure volume V] ℝ) (E →₂[gibbsMeasure volume V] E)).toContinuousLinearMap.comp
        (gibbsSobolevGraph hV hprob).subtypeL)

/-- Each closed Sobolev pair lies in the closure of the compact gradient graph. -/
theorem gibbsSobolev_mem_closure_compactGradient
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u : gibbsSobolevGraph hV hprob) :
    (gibbsSobolevInclusion hV hprob u, gibbsSobolevDerivative hV hprob u) ∈
      closure ((compactGibbsGradient hV.continuous hprob).graph : Set _) := by
  change _ ∈ (compactGibbsGradient hV.continuous hprob).graph.topologicalClosure
  rw [(compactGibbsGradient_isClosable hV hprob).graph_closure_eq_closure_graph]
  exact u.property

/-- The inclusion is injective because the closed graph is an operator graph. -/
theorem gibbsSobolevInclusion_injective {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    Function.Injective (gibbsSobolevInclusion hV hprob) := by
  intro u v huv
  apply Subtype.ext
  apply (WithLp.linearEquiv 2 ℝ
    ((E →₂[gibbsMeasure volume V] ℝ) × (E →₂[gibbsMeasure volume V] E))).injective
  apply Prod.ext huv
  exact (closedGibbsGradient hV hprob).mem_graph_snd_inj' u.property v.property huv

/-- The Sobolev inclusion has dense range in actual Gibbs L², by the proved
smooth compact approximation rather than a density hypothesis. -/
theorem gibbsSobolevInclusion_denseRange {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    DenseRange (gibbsSobolevInclusion hV hprob) := by
  apply (compactGibbsGeneratorDomain_dense V hprob).mono
  intro u hu
  let v : compactGibbsGeneratorDomain V := ⟨u, hu⟩
  let G := compactGibbsGradient hV.continuous hprob
  have hg : (u, G v) ∈ (closedGibbsGradient hV hprob).graph :=
    LinearPMap.le_graph_of_le G.le_closure (G.mem_graph v)
  let w : gibbsSobolevGraph hV hprob := ⟨WithLp.toLp 2 (u, G v), hg⟩
  exact ⟨w, rfl⟩

/-- The actual weighted Dirichlet energy, on the genuine closed Sobolev space. -/
@[expose] noncomputable def gibbsDirichletEnergy {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u v : gibbsSobolevGraph hV hprob) : ℝ :=
  inner ℝ (gibbsSobolevDerivative hV hprob u) (gibbsSobolevDerivative hV hprob v)

/-- The energy is the genuine integral of the closed weak gradients. -/
theorem gibbsDirichletEnergy_eq_integral {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u v : gibbsSobolevGraph hV hprob) :
    gibbsDirichletEnergy hV hprob u v =
      ∫ x, inner ℝ (gibbsSobolevDerivative hV hprob u x)
        (gibbsSobolevDerivative hV hprob v x) ∂gibbsMeasure volume V :=
  L2.inner_def _ _

/-- Exact graph norm identity. Together with completeness, this is the
closedness assertion for the actual nonnegative energy form. -/
theorem gibbsSobolev_norm_sq {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u : gibbsSobolevGraph hV hprob) :
    ‖u‖ ^ 2 = ‖gibbsSobolevInclusion hV hprob u‖ ^ 2 + gibbsDirichletEnergy hV hprob u u := by
  change ‖u.val‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change _ + _ = _ + inner ℝ (gibbsSobolevDerivative hV hprob u) (gibbsSobolevDerivative hV hprob u)
  rw [real_inner_self_eq_norm_sq]
  rfl

/-- Symmetry of the actual closed energy. -/
theorem gibbsDirichletEnergy_symmetric {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u v : gibbsSobolevGraph hV hprob) :
    gibbsDirichletEnergy hV hprob u v = gibbsDirichletEnergy hV hprob v u := real_inner_comm _ _

/-- Nonnegativity of the actual closed energy. -/
theorem gibbsDirichletEnergy_nonneg {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u : gibbsSobolevGraph hV hprob) :
    0 ≤ gibbsDirichletEnergy hV hprob u u := real_inner_self_nonneg

/-- Additivity of the actual closed energy. -/
theorem gibbsDirichletEnergy_add_left {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u v w : gibbsSobolevGraph hV hprob) :
    gibbsDirichletEnergy hV hprob (u + v) w =
      gibbsDirichletEnergy hV hprob u w + gibbsDirichletEnergy hV hprob v w := by
  simp only [gibbsDirichletEnergy, map_add, inner_add_left]

/-- Scalar linearity of the actual closed energy. -/
theorem gibbsDirichletEnergy_smul_left {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (r : ℝ) (u v : gibbsSobolevGraph hV
      hprob) :
    gibbsDirichletEnergy hV hprob (r • u) v = r * gibbsDirichletEnergy hV hprob u v := by
  simp only [gibbsDirichletEnergy, map_smul, real_inner_smul_left]

/-- Continuity in the graph Hilbert topology. -/
theorem gibbsDirichletEnergy_continuous {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    Continuous (fun p : gibbsSobolevGraph hV hprob × gibbsSobolevGraph hV hprob =>
      gibbsDirichletEnergy hV hprob p.1 p.2) :=
  ((gibbsSobolevDerivative hV hprob).continuous.comp continuous_fst).inner
    ((gibbsSobolevDerivative hV hprob).continuous.comp continuous_snd)

/-- The graph Hilbert inner product is exactly L² pairing plus closed energy. -/
theorem gibbsSobolev_inner {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u v : gibbsSobolevGraph hV hprob) :
    inner ℝ u v = inner ℝ (gibbsSobolevInclusion hV hprob u) (gibbsSobolevInclusion hV hprob v) +
      gibbsDirichletEnergy hV hprob u v := rfl

/-- The genuine variational resolvent, constructed by Hilbert Riesz via the
adjoint of the actual dense Sobolev inclusion. -/
@[expose] noncomputable def gibbsWeakResolvent {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    (E →₂[gibbsMeasure volume V] ℝ) →L[ℝ] gibbsSobolevGraph hV hprob :=
  (gibbsSobolevInclusion hV hprob).adjoint

/-- For every actual L² right-hand side, the constructed H¹ element solves
the full variational `(I+A)` equation against every genuine Sobolev test. -/
theorem gibbsWeakResolvent_equation {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (f : E →₂[gibbsMeasure volume V] ℝ) (v : gibbsSobolevGraph hV hprob) :
    inner ℝ (gibbsSobolevInclusion hV hprob (gibbsWeakResolvent hV hprob f))
        (gibbsSobolevInclusion hV hprob v) +
      gibbsDirichletEnergy hV hprob (gibbsWeakResolvent hV hprob f) v =
      inner ℝ f (gibbsSobolevInclusion hV hprob v) := by
  rw [← gibbsSobolev_inner]
  exact ContinuousLinearMap.adjoint_inner_left (gibbsSobolevInclusion hV hprob) v f

/-- The actual weighted variational solution exists uniquely for every L²
right-hand side. No spectral-gap or elliptic-regularity theorem is assumed. -/
theorem existsUnique_gibbs_variational_solution {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (f : E →₂[gibbsMeasure volume V] ℝ) :
    ∃! u : gibbsSobolevGraph hV hprob, ∀ v : gibbsSobolevGraph hV hprob,
      inner ℝ (gibbsSobolevInclusion hV hprob u) (gibbsSobolevInclusion hV hprob v) +
        gibbsDirichletEnergy hV hprob u v = inner ℝ f (gibbsSobolevInclusion hV hprob v) := by
  refine ⟨gibbsWeakResolvent hV hprob f, gibbsWeakResolvent_equation hV hprob f, ?_⟩
  intro u hu
  apply ext_inner_right ℝ
  intro v
  rw [gibbsSobolev_inner, hu, gibbsSobolev_inner, gibbsWeakResolvent_equation]

/-- The bounded actual L² resolvent obtained from the genuine closed energy. -/
@[expose] noncomputable def gibbsL2Resolvent {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    (E →₂[gibbsMeasure volume V] ℝ) →L[ℝ] (E →₂[gibbsMeasure volume V] ℝ) :=
  (gibbsSobolevInclusion hV hprob).comp (gibbsWeakResolvent hV hprob)

/-- The genuine L² resolvent is symmetric. -/
theorem gibbsL2Resolvent_symmetric {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (f g : E →₂[gibbsMeasure volume V] ℝ) :
    inner ℝ (gibbsL2Resolvent hV hprob f) g = inner ℝ f (gibbsL2Resolvent hV hprob g) := by
  change inner ℝ ((gibbsSobolevInclusion hV hprob) ((gibbsSobolevInclusion hV hprob).adjoint f)) g
    = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  exact ContinuousLinearMap.adjoint_inner_left (gibbsSobolevInclusion hV hprob)
    ((gibbsSobolevInclusion hV hprob).adjoint g) f

/-- Positivity of the actual resolvent follows from its Hilbert construction. -/
theorem gibbsL2Resolvent_nonneg {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (f : E →₂[gibbsMeasure volume V] ℝ) :
    0 ≤ inner ℝ f (gibbsL2Resolvent hV hprob f) := by
  have hh := ContinuousLinearMap.adjoint_inner_left (gibbsSobolevInclusion hV hprob)
    ((gibbsSobolevInclusion hV hprob).adjoint f) f
  change 0 ≤ inner ℝ f ((gibbsSobolevInclusion hV hprob) ((gibbsSobolevInclusion hV hprob).adjoint
    f))
  rw [← hh]
  exact real_inner_self_nonneg

end CutoffRigidity
