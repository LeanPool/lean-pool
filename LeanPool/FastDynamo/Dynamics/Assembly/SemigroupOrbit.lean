/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Assembly.PhysicalInductionUniqueness

/-!
# "Its solution": the real datum evolves along the semigroup orbit

The paper states the exact growth law of the *real* datum (`eq:main-thm-growth`):

```
  ‖B^ε(t)‖_{L²(T³)} = e^{t Re λ_ε} ‖B_in^ε‖_{L²(T³)}        (t ≥ 0),
```

for `B_in^ε = Re V^ε` and **its** solution `B^ε`.  The paper's well-posedness statement is the
generation of the induction semigroup on `L²_σ` (§1.1, proved in `lem:semigroup-spectral-growth`),
so "its solution" is `e^{t L_{ε,u}} B_in^ε`.  This module proves that this orbit is the explicit
real curve, that it obeys the law, and that it is the only solution of the curl-form induction
equation with datum `B_in^ε` in the class of forward strong solutions below.

## What is proved

* `productInductionSemigroup_realifiedEigenTrajectoryH2` — the semigroup orbit of the real
  datum **is** the explicit real curve `B^ε(t) = Re(e^{tλ}V^ε)`.  The curve is a strong
  solution of the auxiliary operator (`realifiedEigenTrajectoryH2_isStrongSolution`,
  `FastDynamo/Finish/RealSolution.lean`), the semigroup's own orbit is one too
  (`DomainOperatorSemigroupRealization.domainOrbit_isForwardStrongSolution`), they share an
  initial state, and forward strong solutions of the auxiliary operator are unique
  (`productInductionOperator_forwardStrongSolutionsUnique`).
* `solenoidalInductionSemigroup_realifiedEigenTrajectoryH2` — the same identity for the
  semigroup on `L²_σ`, whose growth bound is the paper's `γ(u, ε)` and whose generator is the
  paper's `L_{ε,u}` with domain `H² ∩ L²_σ` (`generator_solenoidalInductionSemigroup`,
  `FastDynamo/Dynamics/Assembly/SolenoidalGenerator.lean`).
* `norm_solenoidalInductionSemigroup_realAxialOrbit` — the exact growth law
  `eq:main-thm-growth` for that orbit, obtained from the real-side law
  (`ConditionalModeCertificate.realTrajectory_norm`, which is `lem:real-axial-mode`) through
  the isometry `norm_complexifyProductR3L2`.
* `productH2Embedding_eq_solenoidalInductionSemigroup_of_isForwardStrongSolution` — every
  forward strong solution of the curl-form operator `productPhysicalInductionOperator u ε`
  whose initial value lies in `L²_σ` is the semigroup orbit of that value
  (`productH2Embedding_eq_productInductionSemigroup_of_isForwardStrongSolution`,
  `FastDynamo/Dynamics/Assembly/PhysicalInductionUniqueness.lean`).
* `MainSemigroupOrbitClauses` and `mainSemigroupOrbitClauses_of_mainReducedClauses` — the
  orbit clauses, the uniqueness clause and the physical clauses `MainPhysicalClausesAt` at one
  triple `(K, λ, b)`; the packaging consumed by `FastDynamo/MainTheoremStrengthened.lean` and
  `FastDynamo/MainTheoremNormalized.lean`.

## The solution class

A solution of the curl-form equation is a forward strong solution of
`productPhysicalInductionOperator u ε` (`DomainOperator.IsForwardStrongSolution`): a curve
`w : ℝ → H²(T² × T; ℂ³)` whose embedding in the Fourier model of `H⁻²` has, at every `t ≥ 0`,
derivative `ε Δ w(t) + curl(u × w(t))` within `[0, ∞)` (one-sided at `t = 0`).  Only times
`t ≥ 0` enter, no divergence condition is imposed on the curve, and the torus is the product
model `T² × T` with an axially independent velocity.  The paper names no solution class: its
proof of `thm:main` writes the solution down.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

variable (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε)

/-! ## The orbit of the real part of an eigenmode -/

/-- **The semigroup orbit of the real datum is the explicit real curve.**  For an eigenpair
`(λ, V)` of the auxiliary induction operator and every `t ≥ 0`,

```
  e^{t L} (Re V) = Re (e^{tλ} V) .
```

Both sides are forward strong solutions of `productInductionOperator u ε` with the same
initial state — the left by `DomainOperatorSemigroupRealization`, the right by
`realifiedEigenTrajectoryH2_isStrongSolution` — and forward strong solutions of that operator
are unique for `0 ≤ ε` without any further hypothesis
(`productInductionOperator_forwardStrongSolutionsUnique`, the energy competition).

This is the Lean form of the definite article in "**its** solution" of `eq:main-thm-growth`. -/
theorem productInductionSemigroup_realifiedEigenTrajectoryH2 (lam : ℂ) (B : ProductC3H2)
    (hpair : (productInductionOperator u ε).IsEigenpair lam B) {t : ℝ} (ht : 0 ≤ t) :
    productInductionSemigroup u hu hε (Real.toNNReal t)
        (productH2Embedding (productRealPartH2 B)) =
      productH2Embedding (realifiedEigenTrajectoryH2 lam B t) := by
  have hW : (productInductionOperator u ε).IsForwardStrongSolution
      (realifiedEigenTrajectoryH2 lam B) :=
    DomainOperator.IsStrongSolution.isForwardStrongSolution _
      (realifiedEigenTrajectoryH2_isStrongSolution u ε lam B hpair)
  have horb := (productInductionRealization u hu hε).domainOrbit_isForwardStrongSolution
    (productRealPartH2 B)
  have hinit : (productInductionOperator u ε).embedding
        ((productInductionRealization u hu hε).domainOrbit (productRealPartH2 B) 0) =
      (productInductionOperator u ε).embedding (realifiedEigenTrajectoryH2 lam B 0) := by
    rw [(productInductionRealization u hu hε).domainOrbit_zero,
      realifiedEigenTrajectoryH2_zero]
  have huniq := productInductionOperator_forwardStrongSolutionsUnique u hu hε.le
    ((productInductionRealization u hu hε).domainOrbit (productRealPartH2 B))
    (realifiedEigenTrajectoryH2 lam B) horb hW hinit t ht
  have hsg := (productInductionRealization u hu hε).semigroup_eq_embedding_domainOrbit
    (productRealPartH2 B) t ht
  exact hsg.trans huniq

/-- **The same identity on `L²_σ`.**  The induction semigroup on the solenoidal subspace — the
one whose growth bound is the paper's `γ(u, ε)` — is the restriction of the ambient
semigroup, so its orbit is the ambient orbit read through the inclusion. -/
theorem solenoidalInductionSemigroup_realifiedEigenTrajectoryH2 (lam : ℂ) (B : ProductC3H2)
    (hpair : (productInductionOperator u ε).IsEigenpair lam B)
    (Bin : productSolenoidalSubspace)
    (hBin : (Bin : ProductC3L2) = productH2Embedding (productRealPartH2 B))
    {t : ℝ} (ht : 0 ≤ t) :
    ((solenoidalInductionSemigroup u hu hε (Real.toNNReal t) Bin : ProductC3L2)) =
      productH2Embedding (realifiedEigenTrajectoryH2 lam B t) := by
  rw [solenoidalInductionSemigroup_apply, hBin]
  exact productInductionSemigroup_realifiedEigenTrajectoryH2 u hu hε lam B hpair ht

/-! ## The exact growth law of the orbit -/

/-- **`eq:main-thm-growth` for the semigroup orbit**:
for the real datum `B_in^ε = Re V^ε` of an axial eigenmode, the orbit under the induction
semigroup on `L²_σ` obeys

```
  ‖e^{t L} B_in^ε‖ = e^{t Re λ_ε} ‖B_in^ε‖        (t ≥ 0).
```

The orbit is the explicit real curve by
`solenoidalInductionSemigroup_realifiedEigenTrajectoryH2`, that curve is the complexification
of the real `L²` curve `realAxialTrajectory` (`real_field_embedding` of the certificate),
complexification is an isometry (`norm_complexifyProductR3L2`), and the real curve obeys the
exact law by `lem:real-axial-mode` (`realTrajectory_norm`). -/
theorem norm_solenoidalInductionSemigroup_realAxialOrbit (K : ℤ) (lam : ℂ)
    (b : TransverseC3H2) {g : ℝ}
    (cert : RealStrongModeCertificate u ε K lam b g)
    (Bin : productSolenoidalSubspace)
    (hBin : (Bin : ProductC3L2) =
      productH2Embedding (productRealPartH2 (axialLiftH2 K b)))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖solenoidalInductionSemigroup u hu hε (Real.toNNReal t) Bin‖ =
      Real.exp (t * lam.re) * ‖Bin‖ := by
  have horbit := solenoidalInductionSemigroup_realifiedEigenTrajectoryH2 u hu hε lam
    (axialLiftH2 K b) cert.conditional.auxiliaryEigenpair Bin hBin ht
  have hcurve : ‖solenoidalInductionSemigroup u hu hε (Real.toNNReal t) Bin‖ =
      ‖realAxialTrajectory K lam (transverseH2Embedding b) t‖ := by
    have hcoe : ‖solenoidalInductionSemigroup u hu hε (Real.toNNReal t) Bin‖ =
        ‖((solenoidalInductionSemigroup u hu hε (Real.toNNReal t) Bin : ProductC3L2))‖ := rfl
    rw [hcoe, horbit, ← cert.real_field_embedding t, norm_complexifyProductR3L2]
  have hinit : ‖Bin‖ = ‖realAxialInitialField K (transverseH2Embedding b)‖ := by
    have hcoe : ‖Bin‖ = ‖((Bin : ProductC3L2))‖ := rfl
    rw [hcoe, hBin, ← cert.initial_state, ← cert.real_field_embedding 0,
      norm_complexifyProductR3L2, realAxialTrajectory_zero]
  rw [hcurve, hinit]
  exact cert.conditional.realTrajectory_norm t

/-! ## Every solution of the curl form is the orbit -/

/-- **Every solution of the curl-form equation with datum in `L²_σ` is the semigroup orbit.**
If `w` is a forward strong solution of the curl-form induction operator
`productPhysicalInductionOperator u ε` (an `H²`-valued curve, differentiable in the Fourier
model of `H⁻²` within `[0, ∞)`) whose initial value is the element `Bin` of `L²_σ`, then
`w(t) = e^{tL_{ε,u}} Bin` for every `t ≥ 0`.  The divergence-free datum makes `w` the orbit of
the ambient induction semigroup
(`productH2Embedding_eq_productInductionSemigroup_of_isForwardStrongSolution`), and the
semigroup on `L²_σ` is its restriction. -/
theorem productH2Embedding_eq_solenoidalInductionSemigroup_of_isForwardStrongSolution
    {w : ℝ → ProductC3H2}
    (hw : (productPhysicalInductionOperator u ε).IsForwardStrongSolution w)
    (Bin : productSolenoidalSubspace) (hw0 : productH2Embedding (w 0) = (Bin : ProductC3L2))
    {t : ℝ} (ht : 0 ≤ t) :
    productH2Embedding (w t) =
      ((solenoidalInductionSemigroup u hu hε (Real.toNNReal t) Bin : ProductC3L2)) := by
  have hmem : productH2Embedding (w 0) ∈ productSolenoidalSubspace := hw0 ▸ Bin.2
  have hdiv : productDivergenceFromH2 (w 0) = 0 :=
    (productDivergenceFromH2_eq_zero_iff _).2 ((mem_productSolenoidalSubspace_iff _).1 hmem)
  rw [solenoidalInductionSemigroup_apply, ← hw0]
  exact productH2Embedding_eq_productInductionSemigroup_of_isForwardStrongSolution u hu hε hw
    hdiv ht

/-! ## The packaged clause -/

/-- **The semigroup-orbit and solution clauses of Theorem 1.2** at a fixed divergence-free
velocity `u`, threshold `eps0` and growth floor `gamma0`.

For every `0 < ε ≤ ε₀` there are an axial sector `K_ε ≠ 0`, an eigenvalue `λ_ε` with
`Re λ_ε ≥ γ₀` and a non-zero amplitude `b^ε` such that the real datum
`B_in^ε = Re V^ε` of the mode `V^ε = e^{2πiK_εx₃}b^ε`

* lies in `L²_σ(T³)`, the paper's state space, as the element `Bin` of the existential,
* is non-zero,
* has the property that its orbit under the induction semigroup `e^{tL_{ε,u}}` on `L²_σ` is the
  explicit real curve `B^ε(t) = Re(e^{tλ_ε}V^ε)` and obeys the exact growth law
  `eq:main-thm-growth`,

```
  ‖e^{t L_{ε,u}} B_in^ε‖ = e^{t Re λ_ε} ‖B_in^ε‖        (t ≥ 0),
```

* and, for **every** solution `w` of the curl-form induction equation with `w(0) = B_in^ε` —
  every forward strong solution of `productPhysicalInductionOperator u eps`, see the module
  docstring for the class — and every `t ≥ 0`, `w(t) = e^{tL_{ε,u}} B_in^ε`,
  `‖w(t)‖ = e^{t Re λ_ε} ‖B_in^ε‖` and `e^{t γ₀} ‖B_in^ε‖ ≤ ‖w(t)‖`,
* and the same triple `(K_ε, λ_ε, b^ε)` satisfies every clause of
  `MainPhysicalClausesAt u gamma0 eps K lambda b` (`FastDynamo/Main.lean`): `V^ε` is a
  divergence-free eigenmode of the auxiliary and of the curl-form operator with eigenvalue
  `λ_ε`, and the explicit real curve `B^ε(t)` — whose `H²` representative is the curve of the
  orbit identity above — is a strong solution of the curl-form equation, hence one of the
  solutions `w` of the previous item.

The fourth item is the theorem's "**its** solution satisfies `eq:main-thm-growth`" with the
definite article, and the last one places the eigenmode, the real datum and that solution at
one triple.  The predicate therefore contains the physical clauses of `MainPhysicalClauses`
at the same triple.  It is not part of `MainPhysicalClauses` (`FastDynamo/Main.lean`):
`FastDynamo/Main.lean` is imported by the resolvent chain that builds the semigroup, so naming
`solenoidalInductionSemigroup` there would close an import cycle.  It is therefore a separate
predicate, asserted at the theorem's witnesses as the field `semigroupOrbit` of
`MainTheoremStrengthened` and at the normalised velocity as the field `semigroupOrbit` of
`MainTheoremNormalized`. -/
def MainSemigroupOrbitClauses (u : TransverseRealW1Inf)
    (hu : IsTransverseDivergenceFree u) (eps0 gamma0 : ℝ) : Prop :=
  ∀ (eps : ℝ) (heps : 0 < eps), eps ≤ eps0 →
    ∃ (K : ℤ) (lambda : ℂ) (b : TransverseC3H2) (Bin : productSolenoidalSubspace),
      K ≠ 0 ∧ gamma0 ≤ lambda.re ∧ b ≠ 0 ∧
      (reducedInductionOperator u eps K).IsEigenpair lambda b ∧
      (Bin : ProductC3L2) =
        productH2Embedding (productRealPartH2 (axialLiftH2 K b)) ∧
      Bin ≠ 0 ∧
      (∀ t : ℝ, 0 ≤ t →
        ((solenoidalInductionSemigroup u hu heps (Real.toNNReal t) Bin : ProductC3L2)) =
          productH2Embedding (realifiedEigenTrajectoryH2 lambda (axialLiftH2 K b) t)) ∧
      (∀ t : ℝ, 0 ≤ t →
        ‖solenoidalInductionSemigroup u hu heps (Real.toNNReal t) Bin‖ =
          Real.exp (t * lambda.re) * ‖Bin‖) ∧
      (∀ w : ℝ → ProductC3H2,
        (productPhysicalInductionOperator u eps).IsForwardStrongSolution w →
        productH2Embedding (w 0) = (Bin : ProductC3L2) →
        ∀ t : ℝ, 0 ≤ t →
          productH2Embedding (w t) =
              ((solenoidalInductionSemigroup u hu heps (Real.toNNReal t) Bin : ProductC3L2)) ∧
            ‖productH2Embedding (w t)‖ = Real.exp (t * lambda.re) * ‖Bin‖ ∧
            Real.exp (t * gamma0) * ‖Bin‖ ≤ ‖productH2Embedding (w t)‖) ∧
      MainPhysicalClausesAt u gamma0 eps K lambda b

/-- **The semigroup-orbit and solution clauses follow from the reduced clauses**, through the
same finish layer that supplies `MainPhysicalClauses`:
`realStrongModeCertificate_of_reducedEigenpair` gives the real curve, its solenoidality and
the exact real norm law, this module's two orbit theorems turn the curve into the semigroup
orbit, `productH2Embedding_eq_solenoidalInductionSemigroup_of_isForwardStrongSolution`
identifies every solution of the curl form with that orbit, and
`mainPhysicalClausesAt_of_reducedEigenpair` gives the physical clauses at the same triple. -/
theorem mainSemigroupOrbitClauses_of_mainReducedClauses {eps0 gamma0 : ℝ}
    (hgamma0 : 0 < gamma0) (hmode : MainReducedClauses u eps0 gamma0) :
    MainSemigroupOrbitClauses u hu eps0 gamma0 := by
  intro eps heps hle
  obtain ⟨K, lambda, b, hK, hgrowth, hpair⟩ := hmode eps heps hle
  have hb : b ≠ 0 := by
    intro hb
    exact hpair.1 (by rw [hb, map_zero])
  have cert : RealStrongModeCertificate u eps K lambda b gamma0 :=
    realStrongModeCertificate_of_reducedEigenpair u hu eps heps.le K hK lambda
      (lt_of_lt_of_le hgamma0 hgrowth) b hpair gamma0 hgrowth
  have hdiv : productDivergenceFromH2
      (realifiedEigenTrajectoryH2 lambda (axialLiftH2 K b) 0) = 0 :=
    cert.state_solenoidal 0
  have hmem : productH2Embedding (productRealPartH2 (axialLiftH2 K b)) ∈
      productSolenoidalSubspace := by
    rw [mem_productSolenoidalSubspace_iff]
    rw [← cert.initial_state]
    exact (productDivergenceFromH2_eq_zero_iff _).1 hdiv
  refine ⟨K, lambda, b, ⟨_, hmem⟩, hK, hgrowth, hb, hpair, rfl, ?_, ?_, ?_, ?_,
    mainPhysicalClausesAt_of_reducedEigenpair hu hgamma0 heps hK hgrowth hpair⟩
  · have hne : realAxialInitialField K (transverseH2Embedding b) ≠ 0 :=
      cert.conditional.realInitial_ne_zero
    intro hzero
    apply hne
    have hcoe : ((⟨_, hmem⟩ : productSolenoidalSubspace) : ProductC3L2) = 0 := by
      rw [hzero]
      rfl
    have hz : complexifyProductR3L2 (realAxialInitialField K (transverseH2Embedding b)) = 0 := by
      rw [← realAxialTrajectory_zero K lambda (transverseH2Embedding b),
        cert.real_field_embedding 0, cert.initial_state]
      exact hcoe
    exact (complexifyProductR3L2_eq_zero_iff _).1 hz
  · intro t ht
    exact solenoidalInductionSemigroup_realifiedEigenTrajectoryH2 u hu heps lambda
      (axialLiftH2 K b) cert.conditional.auxiliaryEigenpair _ rfl ht
  · intro t ht
    exact norm_solenoidalInductionSemigroup_realAxialOrbit u hu heps K lambda b cert _ rfl ht
  · intro w hw hw0 t ht
    have horb := productH2Embedding_eq_solenoidalInductionSemigroup_of_isForwardStrongSolution
      u hu heps hw _ hw0 ht
    have hnorm := norm_solenoidalInductionSemigroup_realAxialOrbit u hu heps K lambda b cert
      ⟨_, hmem⟩ rfl ht
    have hnorm' : ‖productH2Embedding (w t)‖ =
        Real.exp (t * lambda.re) * ‖(⟨_, hmem⟩ : productSolenoidalSubspace)‖ := by
      rw [horb]
      exact hnorm
    refine ⟨horb, hnorm', ?_⟩
    rw [hnorm']
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hgrowth ht)) (norm_nonneg _)

end

end FastDynamo
