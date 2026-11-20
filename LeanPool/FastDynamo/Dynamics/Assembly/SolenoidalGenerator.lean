/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Assembly.MainGrowthRate
public import LeanPool.FastDynamo.Dynamics.HilleYosida.GeneratorIdentification

/-!
# The generator of the induction semigroup on `L²_σ`

The paper defines the curl-form operator `L_{ε,u} B = curl (u × B) + ε Δ B`
(`eq:physical-generator`) on `L²_σ` with domain `H² ∩ L²_σ`, states that it generates an analytic
`C₀`-semigroup `e^{tL_{ε,u}}` on `L²_σ` (§1.1, Lemma A.1, `lem:semigroup-spectral-growth`), and
defines `γ(u, ε)` as the growth bound of that semigroup (`eq:semigroup-growth-rate`).  This module
proves that `solenoidalInductionSemigroup`, the semigroup whose growth bound is `gamma`, is this
semigroup: its generator is the operator `L_{ε,u}` on `L²_σ` with domain `H² ∩ L²_σ`, and it is
the only `C₀`-semigroup on `L²_σ` with that generator.

* `solenoidalH2`: the divergence-free `H²` fields, the domain `H² ∩ L²_σ`.
* `solenoidalInductionOperator`: the operator `B ↦ A B` on `L²_σ` with domain `solenoidalH2`,
  where `A = productInductionAction u ε` is the auxiliary (transport–stretching) form of the
  induction operator; `productInductionAction_mem_productSolenoidalSubspace` shows that it takes
  values in `L²_σ`.
* `generator_solenoidalInductionSemigroup`: the generator of `solenoidalInductionSemigroup` is
  `solenoidalInductionOperator`.  It combines `HilleYosidaRay.generator_semigroup` (the
  generator of the Hille–Yosida semigroup on `L²` is `A` with domain `H²`) and the restriction
  lemmas `StronglyContinuousSemigroup.mem_generator_restrict_domain_iff`,
  `StronglyContinuousSemigroup.generator_restrict_apply` (the generator of the restriction to the
  closed invariant subspace `L²_σ` is the part of the generator in `L²_σ`, Engel–Nagel II.2.3).
* `mem_generator_solenoidalInductionSemigroup_domain_iff` and
  `productL2ToHMinus2_generator_solenoidalInductionSemigroup`: the domain of the generator is
  `H² ∩ L²_σ`, and on it the generator is, in `H⁻²`, the curl form
  `productPhysicalInductionAction u ε` of `eq:physical-generator`.
* `eq_solenoidalInductionSemigroup_of_generator_eq`, `gamma_eq_growthBound_of_generator_eq`:
  every `C₀`-semigroup on `L²_σ` with this generator is `solenoidalInductionSemigroup`, so
  `gamma` is its growth bound.
* `exists_isResolvent_generator_solenoidalInductionSemigroup_eq`: on the real ray `r > M_u` the
  generator has a bounded resolvent, the restriction to `L²_σ` of the resolvent of the
  Hille–Yosida ray.

The statements are about the product model `T² × T` and an axially independent velocity, as all
of the development's semigroup statements; the operator is written in the auxiliary form and
identified with the curl form through the `H⁻²` embedding, which is an equivalent formulation of
the paper's operator on `H² ∩ L²_σ` (`productInductionAction_toHMinus2_eq_physical`).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## The domain `H² ∩ L²_σ` and the operator -/

/-- The divergence-free `H²` fields, `H² ∩ L²_σ`: the kernel of the divergence on
`ProductC3H2`.  This is the domain of the paper's `L_{ε,u}` (§1.1). -/
def solenoidalH2 : Submodule ℂ ProductC3H2 := LinearMap.ker productDivergenceFromH2.toLinearMap

/-- Membership in `solenoidalH2` is the vanishing of the divergence. -/
theorem mem_solenoidalH2_iff (B : ProductC3H2) :
    B ∈ solenoidalH2 ↔ productDivergenceFromH2 B = 0 :=
  LinearMap.mem_ker

/-- An `H²` field lies in `L²_σ` exactly when its divergence vanishes. -/
theorem productH2Embedding_mem_productSolenoidalSubspace_iff (B : ProductC3H2) :
    productH2Embedding B ∈ productSolenoidalSubspace ↔ productDivergenceFromH2 B = 0 :=
  (mem_productSolenoidalSubspace_iff _).trans (productDivergenceFromH2_eq_zero_iff B).symm

/-- The auxiliary induction action maps divergence-free `H²` fields into `L²_σ`.  It is
`ε ΔB` plus the lower-order field, which for `div B = 0` is the weak curl `curl (u × B)`; both
terms are divergence-free. -/
theorem productInductionAction_mem_productSolenoidalSubspace (u : TransverseRealW1Inf)
    (hu : IsTransverseDivergenceFree u) (ε : ℝ) (B : ProductC3H2)
    (hB : productDivergenceFromH2 B = 0) :
    productInductionAction u ε B ∈ productSolenoidalSubspace := by
  have hlower : productInductionLowerField u B = productVelocityCrossWeakCurl u B := by
    have h := productInductionLowerField_add_velocityDiv_eq_weakCurl u hu B
    rwa [hB, map_zero, add_zero] at h
  have hlap : productLaplacianFromH2 B ∈ productSolenoidalSubspace := by
    rw [mem_productSolenoidalSubspace_iff]
    intro n k
    rw [productFrequencyDivergenceCoeff_laplacian,
      (productDivergenceFromH2_eq_zero_iff B).1 hB n k, mul_zero]
  rw [productInductionAction_eq_diffusion_add_lower, hlower]
  exact productSolenoidalSubspace.add_mem (productSolenoidalSubspace.smul_mem _ hlap)
    ((mem_productSolenoidalSubspace_iff _).2 (productVelocityCrossWeakCurl_solenoidal u B))

/-- **The induction operator on `L²_σ` with domain `H² ∩ L²_σ`.**  The domain is
`solenoidalH2`, embedded into `L²_σ` by the `H² → L²` embedding, and the operator is the
auxiliary induction action `productInductionAction u ε`, which on `solenoidalH2` takes values in
`L²_σ` (`productInductionAction_mem_productSolenoidalSubspace`) and agrees there, in `H⁻²`, with
the paper's curl form `L_{ε,u} B = curl (u × B) + ε Δ B` (`eq:physical-generator`,
`productInductionAction_toHMinus2_eq_physical`). -/
def solenoidalInductionOperator (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) : DomainOperator productSolenoidalSubspace solenoidalH2 where
  embedding := (productH2Embedding.comp solenoidalH2.subtypeL).codRestrict _ fun B ↦
    (productH2Embedding_mem_productSolenoidalSubspace_iff _).2 ((mem_solenoidalH2_iff _).1 B.2)
  embedding_injective := fun _ _ h ↦
    Subtype.ext (productH2Embedding_injective (congrArg Subtype.val h))
  op := ((productInductionAction u ε).comp solenoidalH2.subtypeL).codRestrict _
    (fun B ↦ productInductionAction_mem_productSolenoidalSubspace u hu ε B B.2)

variable (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε)

/-! ## The generator -/

/-- The generator of the induction semigroup on all of `L²` is the auxiliary induction operator
with domain `H²`.  This is `HilleYosidaRay.generator_semigroup` at the product ray. -/
theorem generator_productInductionSemigroup :
    (productInductionSemigroup u hu hε).generator = (productInductionOperator u ε).toLinearPMap :=
  HilleYosidaRay.generator_semigroup _ _

/-- **The domain of the generator on `L²_σ` is `H² ∩ L²_σ`**: a solenoidal field lies in the
domain of the generator of `solenoidalInductionSemigroup` exactly when it is an `H²` field. -/
theorem mem_generator_solenoidalInductionSemigroup_domain_iff (x : productSolenoidalSubspace) :
    x ∈ (solenoidalInductionSemigroup u hu hε).generator.domain ↔
      ∃ B : ProductC3H2, productH2Embedding B = (x : ProductC3L2) := by
  change x ∈ ((productInductionSemigroup u hu hε).restrict _ _).generator.domain ↔ _
  rw [StronglyContinuousSemigroup.mem_generator_restrict_domain_iff _ _
      isClosed_productSolenoidalSubspace, generator_productInductionSemigroup,
    DomainOperator.mem_toLinearPMap_domain_iff]
  exact Iff.rfl

/-- On its domain the generator of `solenoidalInductionSemigroup` acts as the auxiliary induction
action: at the field `ι B` its value is `productInductionAction u ε B`. -/
theorem coe_generator_solenoidalInductionSemigroup
    (x : (solenoidalInductionSemigroup u hu hε).generator.domain) (B : ProductC3H2)
    (hB : productH2Embedding B = ((x : productSolenoidalSubspace) : ProductC3L2)) :
    (((solenoidalInductionSemigroup u hu hε).generator x : productSolenoidalSubspace) :
        ProductC3L2) = productInductionAction u ε B := by
  have hx : ((x : productSolenoidalSubspace) : ProductC3L2) ∈
      (productInductionSemigroup u hu hε).generator.domain :=
    (StronglyContinuousSemigroup.mem_generator_restrict_domain_iff _ _
      isClosed_productSolenoidalSubspace _ _).1 x.2
  have hx' : ((x : productSolenoidalSubspace) : ProductC3L2) ∈
      (productInductionOperator u ε).toLinearPMap.domain :=
    (DomainOperator.mem_toLinearPMap_domain_iff _ _).2 ⟨B, hB⟩
  refine ((productInductionSemigroup u hu hε).generator_restrict_apply _ _ x hx).trans ?_
  refine ((LinearPMap.ext_iff.1 (generator_productInductionSemigroup u hu hε)).2
    (hf := hx) (hg := hx')).trans ?_
  exact DomainOperator.toLinearPMap_apply_of_embedding_eq _ hx' hB

/-- **The generator of the induction semigroup on `L²_σ` is `L_{ε,u}` with domain `H² ∩ L²_σ`.**
The generator of `solenoidalInductionSemigroup` — the semigroup whose growth bound is `gamma`
(`eq:semigroup-growth-rate`) — is `solenoidalInductionOperator u hu ε`, the operator of
`eq:physical-generator` on `L²_σ` with domain `H² ∩ L²_σ` (§1.1, Lemma A.1,
`lem:semigroup-spectral-growth`), written in its auxiliary form.  The paper obtains the semigroup
by perturbation of `εΔ` (Engel–Nagel III.2.10); here it is the restriction to `L²_σ` of the
Hille–Yosida semigroup of the auxiliary operator on `L²`, whose generator is identified by
`HilleYosidaRay.generator_semigroup` and the restriction theorem Engel–Nagel II.2.3. -/
theorem generator_solenoidalInductionSemigroup :
    (solenoidalInductionSemigroup u hu hε).generator =
      (solenoidalInductionOperator u hu ε).toLinearPMap := by
  refine LinearPMap.ext ?_ ?_
  · ext x
    rw [mem_generator_solenoidalInductionSemigroup_domain_iff,
      DomainOperator.mem_toLinearPMap_domain_iff]
    constructor
    · rintro ⟨B, hB⟩
      have hdiv : productDivergenceFromH2 B = 0 :=
        (productH2Embedding_mem_productSolenoidalSubspace_iff B).1 (hB ▸ x.2)
      exact ⟨⟨B, (mem_solenoidalH2_iff B).2 hdiv⟩, Subtype.ext hB⟩
    · rintro ⟨B, hB⟩
      exact ⟨B, congrArg Subtype.val hB⟩
  · intro x hx hx'
    obtain ⟨B, hB⟩ := (DomainOperator.mem_toLinearPMap_domain_iff _ _).1 hx'
    rw [DomainOperator.toLinearPMap_apply_of_embedding_eq _ hx' hB]
    exact Subtype.ext (coe_generator_solenoidalInductionSemigroup u hu hε ⟨x, hx⟩ B
      (congrArg Subtype.val hB))

/-- **On its domain the generator is the curl form.**  For `x` in the domain of the generator of
`solenoidalInductionSemigroup` and `B` the `H²` field with `ι B = x`, the value of the generator,
read in `H⁻²`, is the paper's `L_{ε,u} B = curl (u × B) + ε Δ B` (`eq:physical-generator`,
`productPhysicalInductionAction`). -/
theorem productL2ToHMinus2_generator_solenoidalInductionSemigroup
    (x : (solenoidalInductionSemigroup u hu hε).generator.domain) (B : ProductC3H2)
    (hB : productH2Embedding B = ((x : productSolenoidalSubspace) : ProductC3L2)) :
    productL2ToHMinus2
        (((solenoidalInductionSemigroup u hu hε).generator x : productSolenoidalSubspace) :
          ProductC3L2) =
      productPhysicalInductionAction u ε B := by
  rw [coe_generator_solenoidalInductionSemigroup u hu hε x B hB]
  exact productInductionAction_toHMinus2_eq_physical u hu ε B
    ((productH2Embedding_mem_productSolenoidalSubspace_iff B).1
      (hB ▸ (x : productSolenoidalSubspace).2))

/-! ## Uniqueness and the growth rate -/

/-- **`e^{tL_{ε,u}}` is unique.**  Every `C₀`-semigroup on `L²_σ` whose generator is the induction
operator with domain `H² ∩ L²_σ` is `solenoidalInductionSemigroup` (a `C₀`-semigroup is
determined by its generator, `StronglyContinuousSemigroup.ext_of_generator_eq`). -/
theorem eq_solenoidalInductionSemigroup_of_generator_eq
    {S : StronglyContinuousSemigroup productSolenoidalSubspace}
    (hS : S.generator = (solenoidalInductionOperator u hu ε).toLinearPMap) :
    S = solenoidalInductionSemigroup u hu hε :=
  StronglyContinuousSemigroup.ext_of_generator_eq
    (hS.trans (generator_solenoidalInductionSemigroup u hu hε).symm)

/-- **`gamma` is the growth bound of the semigroup generated by `L_{ε,u}` on `L²_σ`.**  For every
`C₀`-semigroup on `L²_σ` with generator the induction operator with domain `H² ∩ L²_σ` — there is
exactly one, `solenoidalInductionSemigroup` — its growth bound is `gamma u hu hε`, the paper's
`γ(u, ε)` of `eq:semigroup-growth-rate` (the transport to the literal three-torus does not change
the growth bound, `growthBound_literalInductionSemigroup`). -/
theorem gamma_eq_growthBound_of_generator_eq
    {S : StronglyContinuousSemigroup productSolenoidalSubspace}
    (hS : S.generator = (solenoidalInductionOperator u hu ε).toLinearPMap) :
    gamma u hu hε = S.growthBound := by
  rw [eq_solenoidalInductionSemigroup_of_generator_eq u hu hε hS]
  exact growthBound_literalInductionSemigroup u hu hε

/-! ## The resolvent on the real ray -/

/-- **The resolvent of the generator on `L²_σ`.**  At every real `r > M_u`, with
`M_u = ‖transverseStretchingCoefficient u‖`, the generator of `solenoidalInductionSemigroup` has a
bounded resolvent, and it is the restriction to `L²_σ` of the resolvent of the Hille–Yosida ray
`productHilleYosidaRay` of the auxiliary operator on `L²`. -/
theorem exists_isResolvent_generator_solenoidalInductionSemigroup_eq (r : ℝ)
    (hr : ‖transverseStretchingCoefficient u‖ < r) :
    ∃ R : productSolenoidalSubspace →L[ℂ] productSolenoidalSubspace,
      LinearPMap.IsResolvent (solenoidalInductionSemigroup u hu hε).generator r R ∧
      ∀ x : productSolenoidalSubspace,
        (R x : ProductC3L2) =
          (productHilleYosidaRay u hu hε).resolvent.stateResolvent (r : ℂ) x := by
  set hy := productHilleYosidaRay u hu hε
  have hmem : ∀ x : productSolenoidalSubspace,
      hy.resolvent.inv (r : ℂ) (x : ProductC3L2) ∈ solenoidalH2 := fun x ↦
    (mem_solenoidalH2_iff _).2 ((productH2Embedding_mem_productSolenoidalSubspace_iff _).1
      (stateResolvent_productHilleYosidaRay_mem_productSolenoidalSubspace u hu hε r hr x x.2))
  set inv : productSolenoidalSubspace →L[ℂ] solenoidalH2 :=
    ((hy.resolvent.inv (r : ℂ)).comp productSolenoidalSubspace.subtypeL).codRestrict _ hmem
  let hres : HasResolventOn (solenoidalInductionOperator u hu ε) {(r : ℂ)} :=
    { inv := fun _ ↦ inv
      left_inv := by
        rintro z rfl
        refine ContinuousLinearMap.ext fun B ↦ Subtype.ext ?_
        exact HilleYosidaRay.inv_pencil hy hr (B : ProductC3H2)
      right_inv := by
        rintro z rfl
        refine ContinuousLinearMap.ext fun x ↦ Subtype.ext ?_
        exact DFunLike.congr_fun (hy.resolvent.right_inv (r : ℂ) (hy.mem_ofReal r hr))
          (x : ProductC3L2)
      continuousOn := continuousOn_const }
  refine ⟨hres.stateResolvent (r : ℂ), ?_, fun x ↦ rfl⟩
  rw [generator_solenoidalInductionSemigroup]
  exact DomainOperator.isResolvent_stateResolvent hres rfl

end

end FastDynamo
