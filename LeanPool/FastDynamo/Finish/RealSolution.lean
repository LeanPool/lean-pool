/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.Evolution
public import LeanPool.FastDynamo.Operator.RealCompatibility
public import LeanPool.FastDynamo.Analysis.ProductTransportEnergy

/-!
# Real growing solutions from an unstable axial eigenmode

This module closes the real-solution end of the argument.  Starting from an
eigenpair `(λ, b)` of the reduced auxiliary operator `A_{ε,u,K}` with
`0 < re λ`, it produces the paper's real-valued datum
`B_in^ε = re V^ε` for `V^ε(y, x₃) = e^{2π i K x₃} b(y)`, together with the
real-valued curve

`B^ε(t) = e^{t re λ} · re (e^{i t im λ} e^{2π i K x₃} b)`,

shows that this curve solves the physical induction equation in the weak `H⁻²`
realization, and records its exact exponential norm law
`‖B^ε(t)‖ = e^{t re λ} ‖B_in^ε‖`, valid at every real time.  These are the
real-solution clauses of `MainPhysicalClauses` (`FastDynamo/Main.lean`).

The first step is the auxiliary solenoidality theorem: an unstable eigenfunction of the
*auxiliary* transport/stretching operator is distributionally divergence-free, under the sign
hypothesis `0 ≤ ε`.  The paper has no such statement — it recovers the axial component from
`Div⊥h` in `lem:axial-recovery` (Lemma 8.1) — so the
theorem below is a result of the formalisation, used on this route only to
place the eigenfunction in the state space `L²_σ` for `gamma_ge_gamma0`.  Only afterwards does the
compatibility theorem of `FastDynamo.Operator.Compatibility` transfer the eigenpair to the
physical curl-form operator, so the chain is not circular.  Existence of the displayed curve is
proved directly; no semigroup generation or uniqueness statement is used or claimed anywhere
below.

## Contents

* **Solenoidality of unstable auxiliary eigenfunctions.** The auxiliary solenoidality
  theorem for the `x₃`-independent velocity class:
  `productInductionEigenpair_divergence_eq_zero` and its coefficientwise form
  `productInductionEigenpair_solenoidal`, with the wrapper
  `axiallyIndependent_eigenpair_solenoidal`, which also returns the physical eigenpair.
* **Real trajectories associated with a complex axial mode.** The purely
  algebraic `realAxialInitialField` and `realAxialTrajectory`, their
  identification with the real part of the complex exponential mode, the exact
  norm law `norm_realAxialTrajectory`, nonvanishing, and the growth bound
  `realAxialTrajectory_norm_lower_bound`.
* **Conditional completion of one unstable axial mode.**
  `ConditionalModeCertificate`, bundling the lifted all-frequency auxiliary
  eigenpair, its solenoidality, the physical weak eigenpair and the real-mode
  norm laws, and `conditionalModeCertificate_of_reducedEigenpair`, which
  produces it from a reduced unstable eigenpair.
* **Realified eigenmode trajectories.** `realifiedEigenTrajectoryH2`, the real
  part of the complex exponential mode inside the product Fourier `H²` graph,
  with its conjugation fixedness, its solenoidality and its agreement with the
  real `L²` curve; then the strong-solution theorem
  `realifiedEigenTrajectoryH2_isPhysicalStrongSolution` and the bundled
  `RealStrongModeCertificate` with
  `realStrongModeCertificate_of_reducedEigenpair`.
-/

@[expose] public section

/-!
## Solenoidality of unstable auxiliary eigenfunctions

The auxiliary solenoidality theorem, for the `x₃`-independent velocity class used by the
construction.  The proof starts from the actual auxiliary operator

`ε ΔB - (u · ∇)B + (B · ∇)u`,

not from the curl-form operator whose agreement is only known after
solenoidality.  It takes weak divergence into `H⁻¹`, uses the weak
Leibniz identity to obtain the scalar advection--diffusion equation, and
tests that equation with `div B ∈ H¹`.

The diffusivity hypothesis is `0 ≤ ε`.  This is sharp: the separate
`Finish.NegativeDiffusivity` module constructs a counterexample for every
`ε < 0`.
-/

namespace FastDynamo

noncomputable section

/-- **The divergence core of the auxiliary solenoidality theorem.**  If the auxiliary induction
action of an `H²` field `B` is `z ι B - x` with `x` weakly divergence-free, the diffusivity is
nonnegative and `Re z > 0`, then `B` is divergence-free.

Taking the weak divergence turns the equation into the scalar
advection--diffusion equation for `div B` — the term `x` drops out precisely
because it is divergence-free — and the energy endpoint
`productScalarWeakEigenfunction_eq_zero` forces `div B = 0`.

Both shapes the development needs are instances: the eigenpair statement
`productInductionEigenpair_divergence_eq_zero` below is the case `x = 0`, and
the resolvent statement `stateResolvent_mem_productSolenoidalSubspace_of_re_pos`
(`FastDynamo/Dynamics/Assembly/SolenoidalSubspace.lean`) is the general case. -/
theorem productInductionAction_divergence_eq_zero
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (epsilon : ℝ) (h_epsilon : 0 ≤ epsilon)
    (z : ℂ) (hz : 0 < z.re) (B : ProductC3H2) (x : ProductC3L2)
    (hx : productWeakDivergence x = 0)
    (haction :
      productInductionAction u epsilon B = z • productH2Embedding B - x) :
    productDivergenceFromH2 B = 0 := by
  have hdiv := congrArg productWeakDivergence haction
  rw [productWeakDivergence_productInductionAction u hu, map_sub, map_smul,
    productWeakDivergence_productH2Embedding, hx, sub_zero] at hdiv
  set d : ProductScalarH1 := productDivergenceH1 B with hd
  set transport : ProductScalarHMinus1 :=
    productWeakDivergence
      (productVelocityTimesScalar u (productScalarH1Embedding d))
  have htransport : (transport d).re = 0 :=
    productWeakDivergence_velocityTimesScalar_pair_re_eq_zero u hu d
  have hequation :
      z • productScalarH1ToHMinus1 d =
        -transport + (epsilon : ℂ) • productScalarWeakLaplacian d := by
    rw [← hdiv]
    module
  have hdzero : d = 0 :=
    productScalarWeakEigenfunction_eq_zero transport d z epsilon h_epsilon hz
      htransport hequation
  rw [← productScalarH1Embedding_productDivergenceH1, ← hd, hdzero, map_zero]

/-- The auxiliary solenoidality theorem for the axially independent velocity class used in the
construction: a positive-real-part eigenfunction of the auxiliary induction operator is
divergence-free when diffusivity is nonnegative.

This is `productInductionAction_divergence_eq_zero` at `x = 0`. -/
theorem productInductionEigenpair_divergence_eq_zero
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (epsilon : ℝ) (h_epsilon : 0 ≤ epsilon)
    (eigenvalue : ℂ) (h_eigenvalue : 0 < eigenvalue.re)
    (B : ProductC3H2)
    (h : (productInductionOperator u epsilon).IsEigenpair eigenvalue B) :
    productDivergenceFromH2 B = 0 := by
  refine productInductionAction_divergence_eq_zero u hu epsilon h_epsilon
    eigenvalue h_eigenvalue B 0 (map_zero _) ?_
  rw [sub_zero]
  exact h.2

/-- Coefficientwise solenoidal form of the auxiliary solenoidality
theorem. -/
theorem productInductionEigenpair_solenoidal
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (epsilon : ℝ) (h_epsilon : 0 ≤ epsilon)
    (eigenvalue : ℂ) (h_eigenvalue : 0 < eigenvalue.re)
    (B : ProductC3H2)
    (h : (productInductionOperator u epsilon).IsEigenpair eigenvalue B) :
    IsProductSolenoidal (productH2Embedding B) :=
  (productDivergenceFromH2_eq_zero_iff B).1
    (productInductionEigenpair_divergence_eq_zero u hu epsilon h_epsilon
      eigenvalue h_eigenvalue B h)

/-- Positive-diffusivity specialization of the auxiliary solenoidality theorem.
The name records that the velocity realization is independent of the
axial coordinate, exactly as is the velocity constructed in the paper. -/
theorem axiallyIndependent_positive_eigenfunction_solenoidal
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (epsilon : ℝ) (h_epsilon : 0 < epsilon)
    (eigenvalue : ℂ) (h_eigenvalue : 0 < eigenvalue.re)
    (B : ProductC3H2)
    (h : (productInductionOperator u epsilon).IsEigenpair eigenvalue B) :
    productDivergenceFromH2 B = 0 :=
  productInductionEigenpair_divergence_eq_zero u hu epsilon h_epsilon.le
    eigenvalue h_eigenvalue B h

/-- Complete axially independent specialization of the auxiliary solenoidality theorem,
including the consequence that the auxiliary eigenpair is an
eigenpair of the physical curl-form induction operator. -/
theorem axiallyIndependent_eigenpair_solenoidal
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (epsilon : ℝ) (h_epsilon : 0 ≤ epsilon)
    (eigenvalue : ℂ) (h_eigenvalue : 0 < eigenvalue.re)
    (B : ProductC3H2)
    (h : (productInductionOperator u epsilon).IsEigenpair eigenvalue B) :
    productDivergenceFromH2 B = 0 ∧
      (productPhysicalInductionOperator u epsilon).IsEigenpair eigenvalue B := by
  have hdiv := productInductionEigenpair_divergence_eq_zero u hu epsilon
    h_epsilon eigenvalue h_eigenvalue B h
  exact ⟨hdiv,
    productInductionEigenpair_to_physical u hu epsilon eigenvalue B hdiv h⟩

end

end FastDynamo

/-!
## Real trajectories associated with a complex axial mode

Only the algebraic passage from a complex transverse amplitude and a complex
growth rate to the corresponding real-valued axial trajectory.  No evolution
equation is asserted in this section; the strong-solution statement is in the
section on realified eigenmode trajectories below, which uses the real PDE interface.

For a transverse amplitude `b`, axial frequency `K`, and complex number `λ`,
the trajectory is

`exp (t * re λ) Re (exp (i * t * im λ) exp (2π i K x₃) b)`.

The results below identify it with the real part of the complex exponential
mode, prove its exact norm law, and show that it cannot vanish when `K` and
`b` are nonzero.
-/

namespace FastDynamo

noncomputable section

open MeasureTheory

/-- The real initial field associated with a complex axial mode. -/
def realAxialInitialField (K : ℤ) (b : TransverseC3L2) : ProductR3L2 :=
  phaseAxialFieldL2 K 0 b

/-- The explicit real-valued trajectory associated with a complex axial mode.

This is an algebraic definition; it does not by itself assert that the
trajectory solves an induction equation. -/
def realAxialTrajectory (K : ℤ) (eigenvalue : ℂ)
    (b : TransverseC3L2) (t : ℝ) : ProductR3L2 :=
  Real.exp (t * eigenvalue.re) •
    phaseAxialFieldL2 K (t * eigenvalue.im) b

/--
The real axial trajectory starts at the real initial field `realAxialInitialField K b`, i.e. at
zero phase and unit amplitude.
-/
@[simp]
theorem realAxialTrajectory_zero (K : ℤ) (eigenvalue : ℂ)
    (b : TransverseC3L2) :
    realAxialTrajectory K eigenvalue b 0 = realAxialInitialField K b := by
  simp [realAxialTrajectory, realAxialInitialField]

/-- Coordinatewise real part commutes with multiplication by a real scalar. -/
lemma realPartL2_ofReal_smul (r : ℝ) (f : ProductC3L2) :
    realPartL2 ((r : ℂ) • f) = r • realPartL2 f := by
  apply Lp.ext
  have hleft := realPartL2_coe_ae ((r : ℂ) • f)
  have hin := Lp.coeFn_smul (r : ℂ) f
  have hright := Lp.coeFn_smul r (realPartL2 f)
  have hre := realPartL2_coe_ae f
  filter_upwards [hleft, hin, hright, hre] with x hl hi hr hf
  rw [hl, hr, hi]
  simp only [Pi.smul_apply]
  rw [hf]
  ext i
  simp [vecRe]

/-- Decomposition of a complex exponential into growth and phase factors. -/
lemma complex_exp_real_imaginary_time (t : ℝ) (eigenvalue : ℂ) :
    Complex.exp ((t : ℂ) * eigenvalue) =
      (Real.exp (t * eigenvalue.re) : ℂ) *
        Complex.exp (((t * eigenvalue.im : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos,
    Complex.exp_mul_I, ← Complex.ofReal_exp]
  congr 1
  · congr
    simp
  · congr
    · simp
    · simp

/-- The trajectory is the coordinatewise real part of the corresponding
complex exponentially growing axial mode. -/
theorem realAxialTrajectory_eq_realPart_complexExp
    (K : ℤ) (eigenvalue : ℂ) (b : TransverseC3L2) (t : ℝ) :
    realAxialTrajectory K eigenvalue b t =
      realPartL2
        (Complex.exp ((t : ℂ) * eigenvalue) • axialLiftL2 K b) := by
  rw [complex_exp_real_imaginary_time]
  simp only [mul_smul, realAxialTrajectory, phaseAxialFieldL2]
  rw [realPartL2_ofReal_smul]

/-- The initial real field is nonzero whenever the axial frequency and
complex transverse amplitude are nonzero. -/
theorem realAxialInitialField_ne_zero (K : ℤ) (hK : K ≠ 0)
    {b : TransverseC3L2} (hb : b ≠ 0) :
    realAxialInitialField K b ≠ 0 := by
  simpa [realAxialInitialField] using
    phaseAxialFieldL2_ne_zero K hK 0 hb

/-- The norm of a real axial field is independent of its temporal phase. -/
lemma norm_phaseAxialFieldL2_eq (K : ℤ) (hK : K ≠ 0)
    (phase₁ phase₂ : ℝ) (b : TransverseC3L2) :
    ‖phaseAxialFieldL2 K phase₁ b‖ =
      ‖phaseAxialFieldL2 K phase₂ b‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  exact phaseAxialFieldL2_norm_sq_eq K hK phase₁ phase₂ b

/-- Exact exponential norm law for the explicit real trajectory. -/
theorem norm_realAxialTrajectory (K : ℤ) (hK : K ≠ 0)
    (eigenvalue : ℂ) (b : TransverseC3L2) (t : ℝ) :
    ‖realAxialTrajectory K eigenvalue b t‖ =
      Real.exp (t * eigenvalue.re) * ‖realAxialInitialField K b‖ := by
  rw [realAxialTrajectory, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), realAxialInitialField,
    norm_phaseAxialFieldL2_eq K hK (t * eigenvalue.im) 0 b]

/-- No time can make a nonzero real axial trajectory vanish. -/
theorem realAxialTrajectory_ne_zero (K : ℤ) (hK : K ≠ 0)
    (eigenvalue : ℂ) {b : TransverseC3L2} (hb : b ≠ 0) (t : ℝ) :
    realAxialTrajectory K eigenvalue b t ≠ 0 := by
  intro hzero
  have hnorm := norm_realAxialTrajectory K hK eigenvalue b t
  rw [hzero, norm_zero] at hnorm
  have hinitial : realAxialInitialField K b ≠ 0 :=
    realAxialInitialField_ne_zero K hK hb
  have hpositive : 0 <
      Real.exp (t * eigenvalue.re) * ‖realAxialInitialField K b‖ :=
    mul_pos (Real.exp_pos _) (norm_pos_iff.mpr hinitial)
  linarith

/-- Exponential lower bound when `g` is no larger than the real part of the
complex growth rate. -/
theorem realAxialTrajectory_norm_lower_bound
    (K : ℤ) (hK : K ≠ 0) (eigenvalue : ℂ) (b : TransverseC3L2)
    (g t : ℝ) (hg : g ≤ eigenvalue.re) (ht : 0 ≤ t) :
    Real.exp (t * g) * ‖realAxialInitialField K b‖ ≤
      ‖realAxialTrajectory K eigenvalue b t‖ := by
  rw [norm_realAxialTrajectory K hK]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hg ht)

end

end FastDynamo

/-!
## Conditional completion of one unstable axial mode

The endpoint lemmas for a single reduced eigenpair, composed into one
certificate.  Starting from an eigenpair of the reduced auxiliary operator it
records the lifted all-frequency auxiliary eigenpair, its solenoidality, the
resulting physical weak eigenpair, and the algebraic real-mode norm laws.

In this section the real trajectory is an `L²`-valued algebraic curve, and no
claim that it solves the real induction equation is made: that needs the real
evolution interface and the real-part compatibility theorem, and is proved in
the next section.
-/

namespace FastDynamo

noncomputable section

/-- The conclusions drawn in this section from one unstable reduced axial
eigenpair.  The physical eigenpair is valued in the paper's weak `H⁻²`
realization, while the explicit real trajectory is kept in real `L²`. -/
structure ConditionalModeCertificate
    (u : TransverseRealW1Inf) (epsilon : ℝ) (K : ℤ)
    (eigenvalue : ℂ) (b : TransverseC3H2) (g : ℝ) : Prop where
  /-- The reduced eigenpair lifts to the all-frequency auxiliary
  operator. -/
  auxiliaryEigenpair :
    (productInductionOperator u epsilon).IsEigenpair eigenvalue
      (axialLiftH2 K b)
  /-- The lifted complex eigenfunction is divergence-free. -/
  divergence_eq_zero :
    productDivergenceFromH2 (axialLiftH2 K b) = 0
  /-- After solenoidality is proved, the auxiliary eigenpair transfers to the
  physical weak curl-form operator. -/
  physicalEigenpair :
    (productPhysicalInductionOperator u epsilon).IsEigenpair eigenvalue
      (axialLiftH2 K b)
  /-- The real initial `L²` field obtained from the complex axial mode does
  not vanish. -/
  realInitial_ne_zero :
    realAxialInitialField K (transverseH2Embedding b) ≠ 0
  /-- The explicit real `L²` trajectory never vanishes. -/
  realTrajectory_ne_zero : ∀ t : ℝ,
    realAxialTrajectory K eigenvalue (transverseH2Embedding b) t ≠ 0
  /-- Exact exponential norm law, valid at every real time. -/
  realTrajectory_norm : ∀ t : ℝ,
    ‖realAxialTrajectory K eigenvalue (transverseH2Embedding b) t‖ =
      Real.exp (t * eigenvalue.re) *
        ‖realAxialInitialField K (transverseH2Embedding b)‖
  /-- Growth lower bound at nonnegative times for the supplied rate `g`. -/
  realTrajectory_lower_bound : ∀ t : ℝ, 0 ≤ t →
    Real.exp (t * g) *
        ‖realAxialInitialField K (transverseH2Embedding b)‖ ≤
      ‖realAxialTrajectory K eigenvalue (transverseH2Embedding b) t‖

/-- A reduced unstable eigenpair supplies the complete conditional
single-mode certificate `ConditionalModeCertificate`.

The sign condition on `epsilon` is what the auxiliary solenoidality theorem needs; the
stronger assumption `0 < epsilon` of the construction is therefore sufficient. -/
theorem conditionalModeCertificate_of_reducedEigenpair
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (epsilon : ℝ) (h_epsilon : 0 ≤ epsilon)
    (K : ℤ) (hK : K ≠ 0)
    (eigenvalue : ℂ) (h_eigenvalue : 0 < eigenvalue.re)
    (b : TransverseC3H2)
    (h_reduced :
      (reducedInductionOperator u epsilon K).IsEigenpair eigenvalue b)
    (g : ℝ) (hg : g ≤ eigenvalue.re) :
    ConditionalModeCertificate u epsilon K eigenvalue b g := by
  have h_auxiliary :
      (productInductionOperator u epsilon).IsEigenpair eigenvalue
        (axialLiftH2 K b) :=
    (productInductionEigenpair_axialLiftH2_iff_reduced
      u epsilon K eigenvalue b).2 h_reduced
  have h_solenoidal_and_physical :
      productDivergenceFromH2 (axialLiftH2 K b) = 0 ∧
        (productPhysicalInductionOperator u epsilon).IsEigenpair eigenvalue
          (axialLiftH2 K b) :=
    axiallyIndependent_eigenpair_solenoidal u hu epsilon h_epsilon eigenvalue
      h_eigenvalue (axialLiftH2 K b) h_auxiliary
  have hb : transverseH2Embedding b ≠ 0 := h_reduced.1
  refine
    { auxiliaryEigenpair := h_auxiliary
      divergence_eq_zero := h_solenoidal_and_physical.1
      physicalEigenpair := h_solenoidal_and_physical.2
      realInitial_ne_zero := realAxialInitialField_ne_zero K hK hb
      realTrajectory_ne_zero := ?_
      realTrajectory_norm := ?_
      realTrajectory_lower_bound := ?_ }
  · intro t
    exact realAxialTrajectory_ne_zero K hK eigenvalue hb t
  · intro t
    exact norm_realAxialTrajectory K hK eigenvalue
      (transverseH2Embedding b) t
  · intro t ht
    exact realAxialTrajectory_norm_lower_bound K hK eigenvalue
      (transverseH2Embedding b) g t hg ht

end

end FastDynamo

/-!
## Realified eigenmode trajectories

The real `L²` curve of the previous sections is turned into a curve in the
product Fourier `H²` graph.  The state is the conjugation-fixed real part of the
complex exponential eigenmode.  Two strong-solution equations are then proved,
both from the real-coefficient operator compatibility of
`FastDynamo.Operator.RealCompatibility`:
`realifiedEigenTrajectoryH2_isStrongSolution` for the auxiliary operator
`productInductionOperator u ε` on `H²`, which is what identifies the curve with
the semigroup orbit of its datum
(`FastDynamo/Dynamics/Assembly/SemigroupOrbit.lean`, the definite article in
"*its* solution" in the statement of `thm:main`, just before `eq:main-thm-growth`),
and `realifiedEigenTrajectoryH2_isPhysicalStrongSolution` for the paper's
curl form read in `H⁻²`.
-/

namespace FastDynamo

noncomputable section

/-- The complex-graph representative of the real part of an exponentially
evolving complex `H²` field. -/
def realifiedEigenTrajectoryH2
    (eigenvalue : ℂ) (B : ProductC3H2) (t : ℝ) : ProductC3H2 :=
  productRealPartH2 (Complex.exp ((t : ℂ) * eigenvalue) • B)

/-- At time zero the realified graph trajectory is the real part of the
complex eigenfunction. -/
@[simp] theorem realifiedEigenTrajectoryH2_zero
    (eigenvalue : ℂ) (B : ProductC3H2) :
    realifiedEigenTrajectoryH2 eigenvalue B 0 = productRealPartH2 B := by
  simp [realifiedEigenTrajectoryH2]

/--
The `H²`-graph realified trajectory embeds into `L²` as the real part of the exponentially
rescaled complex field: taking real parts commutes with the graph embedding.
-/
theorem productH2Embedding_realifiedEigenTrajectoryH2
    (eigenvalue : ℂ) (B : ProductC3H2) (t : ℝ) :
    productH2Embedding (realifiedEigenTrajectoryH2 eigenvalue B t) =
      productRealPartL2
        (Complex.exp ((t : ℂ) * eigenvalue) • productH2Embedding B) := by
  rw [realifiedEigenTrajectoryH2,
    productH2Embedding_productRealPartH2, map_smul]

/-- The graph representative of the real part is fixed by conjugation. -/
theorem productConjH2_realifiedEigenTrajectoryH2
    (eigenvalue : ℂ) (B : ProductC3H2) (t : ℝ) :
    productConjH2 (realifiedEigenTrajectoryH2 eigenvalue B t) =
      realifiedEigenTrajectoryH2 eigenvalue B t := by
  change productConjH2
      (productRealPartH2 (Complex.exp ((t : ℂ) * eigenvalue) • B)) =
    productRealPartH2 (Complex.exp ((t : ℂ) * eigenvalue) • B)
  rw [productRealPartH2_apply, map_smul, map_add,
    productConjH2_involutive]
  module

/-- A divergence-free complex field has a divergence-free realified
trajectory at every time. -/
theorem realifiedEigenTrajectoryH2_divergence_eq_zero
    (eigenvalue : ℂ) (B : ProductC3H2)
    (hB : productDivergenceFromH2 B = 0) (t : ℝ) :
    productDivergenceFromH2
        (realifiedEigenTrajectoryH2 eigenvalue B t) = 0 := by
  apply productRealPartH2_preserves_divergenceFree
  rw [map_smul, hB, smul_zero]

/-- The real `L²` axial trajectory is exactly the real field represented by
the realified product `H²` curve. -/
theorem complexify_realAxialTrajectory_eq_realified_embedding
    (K : ℤ) (eigenvalue : ℂ) (b : TransverseC3H2) (t : ℝ) :
    complexifyProductR3L2
        (realAxialTrajectory K eigenvalue (transverseH2Embedding b) t) =
      productH2Embedding
        (realifiedEigenTrajectoryH2 eigenvalue (axialLiftH2 K b) t) := by
  rw [realAxialTrajectory_eq_realPart_complexExp,
    complexifyProductR3L2_realPartL2,
    productH2Embedding_realifiedEigenTrajectoryH2,
    productH2Embedding_axialLiftH2]
  rfl

/-! ## The auxiliary strong-solution equation -/

/-- **The realified eigenmode trajectory solves the auxiliary induction equation.**

The complex exponential curve `e^{tλ}V` is a strong solution of the auxiliary operator
`A = productInductionOperator u ε` because `(λ, V)` is an eigenpair
(`DomainOperator.isStrongSolution_eigenTrajectory`), and the auxiliary action commutes with
the `H²` real-part projection (`productInductionAction_productRealPartH2`), which is a fixed
continuous real-linear map and therefore passes through the Banach-valued derivative.  Hence
the real curve `B^ε(t) = Re(e^{tλ}V)` solves the same equation.

This is the step that turns the real datum's curve into *the* semigroup orbit: together with
forward uniqueness of strong solutions it identifies `B^ε(t)` with `e^{tL}B_in^ε`, which is
how the formalisation reads "its solution" in the statement of `thm:main` (just before
`eq:main-thm-growth`); the paper's proof of `thm:main` makes this identification without
stating a uniqueness theorem for strong solutions.  The identification itself
is `productInductionSemigroup_realifiedEigenTrajectoryH2`
(`FastDynamo/Dynamics/Assembly/SemigroupOrbit.lean`), and every forward strong solution of the
curl-form equation with datum `B_in^ε` is the same orbit (`MainSemigroupOrbitClauses`).

`realifiedEigenTrajectoryH2_isPhysicalStrongSolution` below is the same curve read in `H⁻²`
against the paper's curl form; neither statement subsumes the other. -/
theorem realifiedEigenTrajectoryH2_isStrongSolution
    (u : TransverseRealW1Inf) (epsilon : ℝ) (eigenvalue : ℂ) (B : ProductC3H2)
    (hEigen : (productInductionOperator u epsilon).IsEigenpair eigenvalue B) :
    (productInductionOperator u epsilon).IsStrongSolution
      (realifiedEigenTrajectoryH2 eigenvalue B) := by
  intro t
  have hAux :
      (productInductionOperator u epsilon).IsStrongSolution
        ((productInductionOperator u epsilon).eigenTrajectory eigenvalue B) :=
    (productInductionOperator u epsilon).isStrongSolution_eigenTrajectory eigenvalue B hEigen
  have hReal := hasDerivAt_continuousLinearMap_comp productRealPartL2 (hAux t)
  have hcurve :
      (fun s : ℝ ↦ productRealPartL2
          ((productInductionOperator u epsilon).embedding
            ((productInductionOperator u epsilon).eigenTrajectory eigenvalue B s))) =
        fun s : ℝ ↦ (productInductionOperator u epsilon).embedding
          (realifiedEigenTrajectoryH2 eigenvalue B s) := by
    funext s
    exact (productH2Embedding_productRealPartH2 _).symm
  have hval :
      productRealPartL2
          ((productInductionOperator u epsilon).op
            ((productInductionOperator u epsilon).eigenTrajectory eigenvalue B t)) =
        (productInductionOperator u epsilon).op
          (realifiedEigenTrajectoryH2 eigenvalue B t) :=
    (productInductionAction_productRealPartH2 u epsilon _).symm
  rw [hcurve, hval] at hReal
  exact hReal

/-! ## Physical strong-solution equation -/

/-- Realification of a solenoidal auxiliary eigenmode is an explicit strong
solution of the physical weak induction equation.  This proves existence of
the displayed curve directly; it does not use or claim semigroup uniqueness. -/
theorem realifiedEigenTrajectoryH2_isPhysicalStrongSolution
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (epsilon : ℝ) (eigenvalue : ℂ) (B : ProductC3H2)
    (hB : productDivergenceFromH2 B = 0)
    (hEigen :
      (productInductionOperator u epsilon).IsEigenpair eigenvalue B) :
    (productPhysicalInductionOperator u epsilon).IsStrongSolution
      (realifiedEigenTrajectoryH2 eigenvalue B) := by
  intro t
  let A := productInductionOperator u epsilon
  let Z : ℝ → ProductC3H2 := A.eigenTrajectory eigenvalue B
  let W : ℝ → ProductC3H2 := realifiedEigenTrajectoryH2 eigenvalue B
  have hAux : A.IsStrongSolution Z :=
    A.isStrongSolution_eigenTrajectory eigenvalue B hEigen
  have hRealDeriv :=
    hasDerivAt_continuousLinearMap_comp productRealPartL2 (hAux t)
  have hWeakDeriv :=
    hasDerivAt_continuousLinearMap_comp
      (productL2ToHMinus2.restrictScalars ℝ) hRealDeriv
  have hdivZ : productDivergenceFromH2 (Z t) = 0 := by
    change productDivergenceFromH2
      (Complex.exp ((t : ℂ) * eigenvalue) • B) = 0
    rw [map_smul, hB, smul_zero]
  have hdivW : productDivergenceFromH2 (W t) = 0 := by
    exact productRealPartH2_preserves_divergenceFree hdivZ
  have hWZ : W t = productRealPartH2 (Z t) := by
    rfl
  have hPhysical :
      productPhysicalInductionAction u epsilon (W t) =
        productL2ToHMinus2
          (productRealPartL2 (productInductionAction u epsilon (Z t))) := by
    rw [hWZ]
    exact
      productPhysicalInductionAction_productRealPartH2_of_divergenceFree
        u hu epsilon (Z t) hdivZ
  have hCurve :
      Filter.EventuallyEq (nhds t)
        (fun s : ℝ ↦
          (productPhysicalInductionOperator u epsilon).embedding (W s))
        (fun s : ℝ ↦
          productL2ToHMinus2
            (productRealPartL2 (A.embedding (Z s)))) := by
    filter_upwards [] with s
    change productL2ToHMinus2 (productH2Embedding (W s)) =
      productL2ToHMinus2 (productRealPartL2 (productH2Embedding (Z s)))
    apply congrArg productL2ToHMinus2
    rw [show W s = productRealPartH2 (Z s) by rfl,
      productH2Embedding_productRealPartH2]
  exact (hWeakDeriv.congr_of_eventuallyEq hCurve).congr_deriv hPhysical.symm

/-- Completion of the real-mode slice from a reduced unstable
eigenpair.  It combines the static conditional certificate, a real-valued
`H²` graph representative, its solenoidality, the physical strong-solution
equation, and the exact real `L²` norm law.

The field is represented inside the complex Fourier graph as a fixed point of
conjugation.  Its actual real `L²` value is `realAxialTrajectory`. -/
structure RealStrongModeCertificate
    (u : TransverseRealW1Inf) (epsilon : ℝ) (K : ℤ)
    (eigenvalue : ℂ) (b : TransverseC3H2) (g : ℝ) : Prop where
  conditional : ConditionalModeCertificate u epsilon K eigenvalue b g
  initial_state :
    realifiedEigenTrajectoryH2 eigenvalue (axialLiftH2 K b) 0 =
      productRealPartH2 (axialLiftH2 K b)
  state_fixed : ∀ t : ℝ,
    productConjH2
        (realifiedEigenTrajectoryH2 eigenvalue (axialLiftH2 K b) t) =
      realifiedEigenTrajectoryH2 eigenvalue (axialLiftH2 K b) t
  state_solenoidal : ∀ t : ℝ,
    productDivergenceFromH2
        (realifiedEigenTrajectoryH2 eigenvalue (axialLiftH2 K b) t) = 0
  real_field_embedding : ∀ t : ℝ,
    complexifyProductR3L2
        (realAxialTrajectory K eigenvalue (transverseH2Embedding b) t) =
      productH2Embedding
        (realifiedEigenTrajectoryH2 eigenvalue (axialLiftH2 K b) t)
  physical_strong_solution :
    (productPhysicalInductionOperator u epsilon).IsStrongSolution
      (realifiedEigenTrajectoryH2 eigenvalue (axialLiftH2 K b))

/-- A reduced unstable eigenpair produces the complete explicit real strong
mode certificate. -/
theorem realStrongModeCertificate_of_reducedEigenpair
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (epsilon : ℝ) (h_epsilon : 0 ≤ epsilon)
    (K : ℤ) (hK : K ≠ 0)
    (eigenvalue : ℂ) (h_eigenvalue : 0 < eigenvalue.re)
    (b : TransverseC3H2)
    (h_reduced :
      (reducedInductionOperator u epsilon K).IsEigenpair eigenvalue b)
    (g : ℝ) (hg : g ≤ eigenvalue.re) :
    RealStrongModeCertificate u epsilon K eigenvalue b g := by
  let B : ProductC3H2 := axialLiftH2 K b
  have hconditional := conditionalModeCertificate_of_reducedEigenpair
    u hu epsilon h_epsilon K hK eigenvalue h_eigenvalue b h_reduced g hg
  have hAux :
      (productInductionOperator u epsilon).IsEigenpair eigenvalue B :=
    hconditional.auxiliaryEigenpair
  have hdiv : productDivergenceFromH2 B = 0 :=
    hconditional.divergence_eq_zero
  refine
    { conditional := hconditional
      initial_state := realifiedEigenTrajectoryH2_zero eigenvalue B
      state_fixed := ?_
      state_solenoidal := ?_
      real_field_embedding := ?_
      physical_strong_solution := ?_ }
  · intro t
    exact productConjH2_realifiedEigenTrajectoryH2 eigenvalue B t
  · intro t
    exact realifiedEigenTrajectoryH2_divergence_eq_zero
      eigenvalue B hdiv t
  · intro t
    exact complexify_realAxialTrajectory_eq_realified_embedding
      K eigenvalue b t
  · exact realifiedEigenTrajectoryH2_isPhysicalStrongSolution
      u hu epsilon eigenvalue B hdiv hAux

end

end FastDynamo
