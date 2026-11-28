/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.CategoryTheory.Countable
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# The path distribution of a constructed Markov chain

The forward direction of Saporito's Theorem 1.1.2 gives finite-path
factorization from the Markov property. For the time-homogeneous construction
in this file with initial law `λ` and transition law `P`, the factors give

  `P(X₀ = i₀, …, X_n = i_n) = λ(i₀) · ∏_{k<n} P(i_k, i_{k+1})`.

Earlier the repo carried this as a *definitional* identity (a structure
whose `pathProb` field is defined as the product — honest, but `rfl`).
This file derives it: the chain's law is **constructed** on the space of
infinite trajectories by the Ionescu–Tulcea theorem
(`ProbabilityTheory.Kernel.trajMeasure`, in Mathlib since the current pin),
from kernels that read only the *last* coordinate of the history — that
restriction *is* the Markov property of the construction — and the
factorization of cylinder probabilities is then proved by induction along

  `μ_{n+1}-marginal = μ_n-marginal ⊗ₘ κ_n`

(`Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`),
evaluating the comp-product on the rectangle `{history} ×ˢ {next state}`.

State space: any countable discrete `ι` (Saporito's chains are countable;
finiteness is never needed). Probabilities are stated in `ℝ≥0∞` via `PMF` —
the canonical Mathlib carrier for discrete laws.

## Main definitions

* `markovTransitionKernel`: the kernel from the history up to time `n` to the next state, which
  reads only the last coordinate of the history and applies the one-step law `P`.
* `markovPathMeasure`: the law of the chain `(init, P)` on `ℕ → ι`, by the Ionescu–Tulcea
  construction from `markovTransitionKernel`.
* `pathCylinder`: the set of trajectories that agree with `path` up to time `n`.

## Main results

* `markovPathMeasure_cylinder` — cylinder probabilities of the constructed chain
  factor as `init(path 0) · ∏_{k<n} P(path k)(path (k+1))`, derived from
  the construction.

`Models/Binomial/PathMeasure.lean` uses the chain with `Bernoulli(q)` initial and transition laws as
the law of i.i.d. coin flips, and writes the CRR binomial price as an expectation over its paths.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 1.1.2,
  finite-path factorization direction

## Tags

Markov chain, path distribution, Ionescu–Tulcea theorem, transition probabilities,
cylinder probabilities, initial distribution, MSC 60J10, MSC 28A25
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ENNReal

variable {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]

/-- The history-to-next-state kernel of a time-homogeneous Markov chain with
one-step law `P`: it reads only the **last** coordinate of the history. That
restriction is exactly the Markov property of the resulting construction. -/
noncomputable def markovTransitionKernel (P : ι → PMF ι) (n : ℕ) :
    Kernel (Π _i : Iic n, ι) ι :=
  ⟨fun h ↦ (P (h ⟨n, mem_Iic.mpr le_rfl⟩)).toMeasure,
    measurable_of_countable _⟩

instance (P : ι → PMF ι) (n : ℕ) : IsMarkovKernel (markovTransitionKernel P n) :=
  ⟨fun _ ↦ PMF.toMeasure.isProbabilityMeasure _⟩

/-- The law of the Markov chain `(init, P)` on the space of infinite
trajectories: the Ionescu–Tulcea construction applied to the last-coordinate
kernels. -/
noncomputable def markovPathMeasure (init : PMF ι) (P : ι → PMF ι) :
    Measure (ℕ → ι) :=
  Kernel.trajMeasure init.toMeasure (markovTransitionKernel P)

instance (init : PMF ι) (P : ι → PMF ι) :
    IsProbabilityMeasure (markovPathMeasure init P) :=
  inferInstanceAs (IsProbabilityMeasure
    (Kernel.trajMeasure (X := fun _ : ℕ ↦ ι) init.toMeasure (markovTransitionKernel P)))

/-- The `n`-cylinder along `path`: trajectories agreeing with `path` up to
time `n` — the event `{X₀ = path 0, …, X_n = path n}`. -/
def pathCylinder (path : ℕ → ι) (n : ℕ) : Set (ℕ → ι) :=
  {ω | ∀ k ≤ n, ω k = path k}

omit [Countable ι] in
lemma measurableSet_pathCylinder (path : ℕ → ι) (n : ℕ) :
    MeasurableSet (pathCylinder path n) := by
  have h : pathCylinder path n
      = ⋂ k ∈ Set.Iic n, (fun ω : ℕ → ι ↦ ω k) ⁻¹' {path k} := by
    ext ω
    simp [pathCylinder]
  rw [h]
  exact MeasurableSet.biInter (Set.to_countable _)
    (fun k _ ↦ (measurable_pi_apply k) (measurableSet_singleton _))

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
/-- The cylinder is the `frestrictLe`-preimage of a single restricted path. -/
lemma frestrictLe_preimage_singleton (path : ℕ → ι) (n : ℕ) :
    frestrictLe (π := fun _ ↦ ι) n ⁻¹' {fun i : Iic n ↦ path ↑i}
      = pathCylinder path n := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff,
    frestrictLe_apply, Subtype.forall, mem_Iic, pathCylinder, Set.mem_ofPred_eq]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
/-- Splitting the `(n+1)`-cylinder through the pair map
`ω ↦ (history up to n, state at n+1)`. -/
lemma pairMap_preimage_singleton_prod (path : ℕ → ι) (n : ℕ) :
    (fun ω : ℕ → ι ↦ (frestrictLe n ω, ω (n + 1))) ⁻¹'
        ({fun i : Iic n ↦ path ↑i} ×ˢ {path (n + 1)})
      = pathCylinder path (n + 1) := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, funext_iff,
    frestrictLe_apply, Subtype.forall, mem_Iic, pathCylinder, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h₁, h₂⟩ k hk
    rcases (by omega : k ≤ n ∨ k = n + 1) with hk' | rfl
    · exact h₁ k hk'
    · exact h₂
  · intro h
    exact ⟨fun k hk ↦ h k (by omega), h (n + 1) le_rfl⟩

/-- Comp-product of a measure and a kernel on a rectangle with singleton
base: `(μ ⊗ₘ κ)({a} ×ˢ t) = μ {a} · κ a t`. -/
lemma compProd_singleton_prod {α β : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} [MeasurableSingletonClass α]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    (a : α) {t : Set β} (ht : MeasurableSet t) :
    (μ ⊗ₘ κ) ({a} ×ˢ t) = μ {a} * κ a t := by
  rw [Measure.compProd_apply_prod (measurableSet_singleton a) ht,
    Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac,
    smul_eq_mul]

/-- Base case: the time-0 cylinder has the initial probability. -/
lemma markovPathMeasure_cylinder_zero (init : PMF ι) (P : ι → PMF ι)
    (path : ℕ → ι) :
    markovPathMeasure init P (pathCylinder path 0) = init (path 0) := by
  have hdef : ((default : Iic (0 : ℕ)) : ℕ) = 0 :=
    Nat.le_zero.mp (mem_Iic.mp (default : Iic (0 : ℕ)).2)
  have hset : (MeasurableEquiv.piUnique (fun _ : Iic (0 : ℕ) ↦ ι)).symm ⁻¹'
      {fun i : Iic (0 : ℕ) ↦ path ↑i} = {path 0} := by
    rw [MeasurableEquiv.preimage_symm, Set.image_singleton]
    simp only [MeasurableEquiv.piUnique_apply]
    rw [hdef]
  unfold markovPathMeasure Kernel.trajMeasure
  rw [← frestrictLe_preimage_singleton path 0,
    ← Measure.map_apply (measurable_frestrictLe 0) (measurableSet_singleton _),
    Measure.map_comp _ _ (measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp,
    Measure.map_apply (MeasurableEquiv.measurable _) (measurableSet_singleton _),
    hset]
  exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)

/-- Inductive step: adjoining one transition multiplies the cylinder
probability by the one-step transition probability — the comp-product
recursion of the Ionescu–Tulcea marginals, evaluated on a rectangle. -/
lemma markovPathMeasure_cylinder_succ (init : PMF ι) (P : ι → PMF ι)
    (path : ℕ → ι) (n : ℕ) :
    markovPathMeasure init P (pathCylinder path (n + 1))
      = markovPathMeasure init P (pathCylinder path n)
          * P (path n) (path (n + 1)) := by
  have hpair : Measurable (fun ω : ℕ → ι ↦ (frestrictLe n ω, ω (n + 1))) :=
    (measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
  have hprob : IsProbabilityMeasure
      ((markovPathMeasure init P).map (frestrictLe (π := fun _ ↦ ι) n)) :=
    inferInstance
  unfold markovPathMeasure at hprob ⊢
  rw [← pairMap_preimage_singleton_prod path n,
    ← Measure.map_apply hpair
      ((measurableSet_singleton _).prod (measurableSet_singleton _)),
    ← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    compProd_singleton_prod _ _ _ (measurableSet_singleton _),
    Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton _),
    frestrictLe_preimage_singleton path n]
  congr 1
  rw [show (markovTransitionKernel P n) (fun i : Iic n ↦ path ↑i)
      = (P (path n)).toMeasure from rfl]
  exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)

/-- **Finite-path factorization for the constructed chain.** Under
the Ionescu–Tulcea law of the chain `(init, P)`, every finite-path
probability factors as the initial probability times the product of one-step
transition probabilities:

  `P(X₀ = path 0, …, X_n = path n)
     = init(path 0) · ∏_{k<n} P(path k)(path (k+1))`.

Derived from the construction — the kernels read only the last coordinate,
and the factorization falls out of the comp-product recursion of the
marginals. Not a definition: the left side is a measure of a set of
infinite trajectories. -/
theorem markovPathMeasure_cylinder (init : PMF ι) (P : ι → PMF ι)
    (path : ℕ → ι) (n : ℕ) :
    markovPathMeasure init P (pathCylinder path n)
      = init (path 0) * ∏ k ∈ Finset.range n, P (path k) (path (k + 1)) := by
  induction n with
  | zero => simpa using markovPathMeasure_cylinder_zero init P path
  | succ n ih =>
      rw [markovPathMeasure_cylinder_succ, ih, Finset.prod_range_succ, mul_assoc]

end MathFin
