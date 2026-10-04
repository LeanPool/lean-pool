/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.HigherInterior
public import LeanPool.EllipticPDE.Regularity.SmoothGlue
public import LeanPool.EllipticPDE.Regularity.IteratedFamily
public import LeanPool.EllipticPDE.Embedding.SmoothOfGradClosed


/-!
# Infinite differentiability in the interior

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 3 (*Infinite
differentiability in the interior*, p. 334). Smooth coefficients and a smooth datum give a
solution smooth in the interior, whatever the boundary does.

The route is the one the chapter takes. Higher interior regularity, run at every order, puts
the solution in `H^m(V)` for every `m`; the Sobolev embedding then converts an unbounded supply
of weak derivatives into classical ones. Neither half needs a quantitative statement: the
constants of `higher_interior_regularity` are what make the estimate uniform, and smoothness on
a fixed `V` needs only that the derivatives exist.

## Requirements of the embedding half

Weak derivatives of every order are handed over one family per order, with nothing relating them,
so the embedding half starts by assembling them into a single family closed under
differentiation. Uniqueness of the weak gradient on a ball is what identifies the entries two
families share (`EllipticPdes.Regularity.exists_gradClosed_of_hasIteratedWeakDerivOn`).

From there it is two steps.

* `EllipticPdes.Embedding.memLp_of_gradClosed` raises every member of the family from `L²` to
  `L^{2d}`, iterating the Gagliardo-Nirenberg-Sobolev step and paying a weak derivative per rung.
  Since `2d > d` in every dimension, `EllipticPdes.Embedding.morrey_ball` then puts every member
  in a Hölder class, so the whole family becomes continuous at once.
* A continuous function with a continuous weak gradient is classically differentiable with that
  gradient (`EllipticPdes.Embedding.hasFDerivAt_of_continuousOn_hasWeakGradOn`). The derivative
  of a representative is the representative of the derivative, so an induction on the order reads
  the family as `C^∞` without shrinking the ball again
  (`EllipticPdes.Embedding.contDiffOn_of_gradClosed`).

## Main declarations

* `contDiffOn_interior_of_hasIteratedWeakDerivOn`: weak derivatives of every order give a
  smooth representative on the interior.
* `interior_smooth`: Evans's Theorem 3.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- **Sobolev ladder on a ball.** An `L²` class with weak derivatives of every order has a
smooth representative on any ball whose closure sits inside the region.

This is the analytic content of Evans's Theorem 3, and it is three steps.

* The families of `EllipticPdes.Regularity.HasIteratedWeakDerivOn`, one per order and unrelated
  to each other, become one family closed under differentiation
  (`EllipticPdes.Regularity.exists_gradClosed_of_hasIteratedWeakDerivOn`), by uniqueness of the
  weak gradient on a ball.
* The ladder `EllipticPdes.Embedding.memLp_two_mul_of_gradClosed` raises every member of that
  family from `L²` to `L^{2d}`, which passes `d` in every dimension, so
  `EllipticPdes.Embedding.morrey_ball` gives each a Hölder representative.
* A continuous function with a continuous weak gradient is classically differentiable
  (`EllipticPdes.Embedding.hasFDerivAt_of_continuousOn_hasWeakGradOn`), and the derivative of a
  representative is the representative of the derivative, so an induction on the order reads the
  family as `C^∞` (`EllipticPdes.Embedding.contDiffOn_of_gradClosed`).

The argument is local, so it runs on balls small enough for the ladder to shrink inside, and
`exists_contDiffOn_of_locally_ae` collects the local representatives. The closed ball is asked
for so that every point of the open one has room for that shrinking. -/
theorem exists_contDiffOn_ball_of_hasIteratedWeakDerivOn
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (u : L2D V)
    (h : ∀ k : ℕ, Nonempty (HasIteratedWeakDerivOn V k u))
    {x : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ}
    (hball : Metric.closedBall x r ⊆ interior V) :
    ∃ v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball x r) ∧
        v =ᵐ[volume.restrict (Metric.ball x r)]
          (u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) := by
  have hVsub : Metric.ball x r ⊆ V :=
    ((Metric.ball_subset_closedBall.trans hball).trans interior_subset)
  have hloc : ∀ y ∈ Metric.ball x r, ∃ B : Set (EuclideanSpace ℝ (Fin (n + 1))),
      IsOpen B ∧ y ∈ B ∧ B ⊆ Metric.ball x r ∧
      ∃ w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) w B ∧
        w =ᵐ[volume.restrict B] (u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) := by
    intro y hy
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 Metric.isOpen_ball y hy
    have hr1 : (0 : ℝ) < ρ / 4 := by linarith
    have hr1R1 : ρ / 4 < ρ / 2 := by linarith
    have hsubV : Metric.ball y (ρ / 2) ⊆ V :=
      (Metric.ball_subset_ball (by linarith)).trans (hρsub.trans hVsub)
    obtain ⟨F, hFgrad, hFmem, hF0⟩ := exists_gradClosed_of_hasIteratedWeakDerivOn u h hsubV
    obtain ⟨w, hwsmooth, hwae⟩ :=
      EllipticPdes.Embedding.contDiffOn_of_gradClosed
        (nxt := fun (α : List (Fin (n + 1))) k => k :: α)
        (Nat.succ_pos n) y hr1 hr1R1 hFgrad hFmem
    refine ⟨Metric.ball y (ρ / 4), Metric.isOpen_ball, Metric.mem_ball_self hr1,
      (Metric.ball_subset_ball (by linarith)).trans hρsub, w [], hwsmooth [], ?_⟩
    rw [← hF0]
    exact hwae []
  obtain ⟨v, hvae, hvc⟩ := exists_contDiffOn_of_locally_ae Metric.isOpen_ball _ hloc
  exact ⟨v, hvc, hvae⟩

/-- **Sobolev ladder in qualitative form.** An `L²` class on `V` with weak derivatives of
every order has a representative smooth on the interior of `V`. No bound is asked and none is
produced: the estimate lives in `higher_interior_regularity`, and smoothness on a fixed set
follows from the existence of the derivatives alone.

The proof is local, so it runs on balls inside `interior V` and never sees `V` itself except
through the family it is handed. `exists_contDiffOn_of_locally_ae` assembles the local
representatives, and it needs no gluing: two of them are continuous and agree almost everywhere
where their balls meet, so they agree there. -/
theorem contDiffOn_interior_of_hasIteratedWeakDerivOn
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (u : L2D V)
    (h : ∀ k : ℕ, Nonempty (HasIteratedWeakDerivOn V k u)) :
    ∃ u' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      u' =ᵐ[volume.restrict (interior V)] (u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) u' (interior V) := by
  refine exists_contDiffOn_of_locally_ae isOpen_interior _ fun y hy => ?_
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
  refine ⟨Metric.ball y (r / 2), Metric.isOpen_ball, Metric.mem_ball_self (by linarith),
    (Metric.ball_subset_ball (by linarith)).trans hrsub, ?_⟩
  exact exists_contDiffOn_ball_of_hasIteratedWeakDerivOn u h
    ((Metric.closedBall_subset_ball (by linarith)).trans hrsub)

/-- **Infinite differentiability in the interior (Evans, *Partial Differential Equations*
(2nd ed.), §6.3.1, Theorem 3, p. 334).** For a weak solution of `L u = f` whose coefficients lie
in `W^{k,∞}` at every order and whose datum has weak derivatives of every order in `L²(Ω)`, the
solution has a representative smooth on the interior of each compact `V ⋐ Ω`.

The principal part is asked for once more, as `W^{1,∞}` in the pointwise form of
`IsLipCoeff`, which the base case of `higher_interior_regularity` reads and which no
`W^{k,∞}` bundle supplies: the passage from an essential bound on a weak gradient to the
pointwise Lipschitz estimate is the statement that a `W^{1,∞}` function has a Lipschitz
representative, and Mathlib has Rademacher's theorem in the opposite direction alone. Smooth
coefficients meet every hypothesis through `IsC1Coeff.toIsLipCoeff`,
`IsCkCoeff.toIsWkInftyCoeff` and `IsWkInfty.ofContDiff`, so the classical statement with
`a_{ij}, b_i, c, f ∈ C^∞(Ω)` follows as an instance. -/
theorem interior_smooth (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsLipCoeff Op.toEllipticCoeff)
    (hA : ∀ k : ℕ, IsWkInftyCoeff Op.toEllipticCoeff k)
    (hbc : ∀ k : ℕ, IsWkInftyLower Op k)
    (u : H01 Ω) (f : L2D Ω)
    (hf : ∀ k : ℕ, ∃ hfk : HasIteratedWeakDerivOn Ω k f, ∃ M : ℝ, IteratedL2Bound hfk M)
    (hweak : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ))
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ u' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      u' =ᵐ[volume.restrict (interior V)]
          (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) u' (interior V) := by
  -- Every order of weak differentiability on `V`, from higher interior regularity run at that
  -- order and then cut back down.
  have hall : ∀ k : ℕ, Nonempty (HasIteratedWeakDerivOn V k
      (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)))) := by
    intro k
    obtain ⟨hfk, M, hM⟩ := hf k
    obtain ⟨C, _hC0, hC⟩ :=
      higher_interior_regularity Op hΩm hΩo hA1 k (hA (k + 1)) (hbc k) hVc hVΩ
    obtain ⟨hu, _⟩ := hC u f M hfk hM hweak
    exact ⟨hu.mono (by omega)⟩
  obtain ⟨u', hu'ae, hu'smooth⟩ := contDiffOn_interior_of_hasIteratedWeakDerivOn _ hall
  refine ⟨u', ?_, hu'smooth⟩
  -- The `V`-restriction agrees almost everywhere with the whole-space extension it came from.
  have hres : (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))
        : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
      =ᵐ[volume.restrict (interior V)]
        (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) :=
    (coeFn_restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))).filter_mono
      (ae_mono (Measure.restrict_mono interior_subset le_rfl))
  exact hu'ae.trans hres

end EllipticPdes.Regularity
