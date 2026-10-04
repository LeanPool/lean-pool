/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Embedding.WeakGradUnique
public import LeanPool.EllipticPDE.Embedding.WeakDerivBridge
public import LeanPool.EllipticPDE.Embedding.GagliardoNirenberg
public import LeanPool.EllipticPDE.Regularity.HigherWeakDeriv


/-!
# One family closed under differentiation

Higher interior regularity is proved order by order, so a solution with weak derivatives of every
order arrives as one `EllipticPdes.Regularity.HasIteratedWeakDerivOn` per order, and nothing in
the statement relates the entries two of them share. The Sobolev ladder needs the opposite: a
single family, closed under differentiation, so that the derivative of a member is again a
member.

Uniqueness of the weak gradient supplies the relation. On a ball inside the region the entries
two families assign to one list of directions agree almost everywhere, by induction along the
list, so reading each list off the family of its own length gives a family closed under
differentiation up to a null set, which is all the ladder reads.

## Main declarations

* `EllipticPdes.Regularity.exists_gradClosed_of_hasIteratedWeakDerivOn`: the closed family.
* `EllipticPdes.Regularity.exists_gradClosed_of_hasIteratedWeakDerivOn_le`: the same at a bounded
  order, where one family is the whole supply and no uniqueness is spent.
-/

@[expose] public section

open MeasureTheory Set Metric

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev EllipticPdes.Embedding

variable {d : ℕ}

/-- **Weak derivatives of every order give one family closed under differentiation.** On a ball
inside the region, the functions `F α` read off the order-`α.length` family have, for each
direction `k`, the function `F (k :: α)` as a weak `k`-derivative, and all of them lie in `L²`.
The empty list is the function itself, on the nose.

The induction along the list is where uniqueness is spent: the entries at `α` of two families
agree almost everywhere by the inductive hypothesis, so the two weak gradients they have are
weak gradients of one function, hence agree, which is the inductive step at `k :: α`. -/
theorem exists_gradClosed_of_hasIteratedWeakDerivOn {V : Set (EuclideanSpace ℝ (Fin d))}
    (u : L2D V) (h : ∀ k : ℕ, Nonempty (HasIteratedWeakDerivOn V k u))
    {c : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hBV : Metric.ball c R ⊆ V) :
    ∃ F : List (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ α, HasWeakGradOn (Metric.ball c R) (F α) (fun k => F (k :: α))) ∧
      (∀ α, MemLp (F α) 2 (volume.restrict (Metric.ball c R))) ∧
      F [] = (u : EuclideanSpace ℝ (Fin d) → ℝ) := by
  classical
  have : IsFiniteMeasure (volume.restrict (Metric.ball c R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  set H : ∀ k : ℕ, HasIteratedWeakDerivOn V k u := fun k => (h k).some with hH_def
  have hmemball : ∀ X : L2D V,
      MemLp (X : EuclideanSpace ℝ (Fin d) → ℝ) 2 (volume.restrict (Metric.ball c R)) :=
    fun X => (Lp.memLp X).mono_measure (Measure.restrict_mono hBV le_rfl)
  have hint : ∀ X : L2D V,
      IntegrableOn (X : EuclideanSpace ℝ (Fin d) → ℝ) (Metric.ball c R) volume :=
    fun X => (hmemball X).integrable (by norm_num)
  have hgradV : ∀ (m : ℕ) (α : List (Fin d)), α.length < m →
      HasWeakGradOn (Metric.ball c R) ((H m).D α : EuclideanSpace ℝ (Fin d) → ℝ)
        (fun k => ((H m).D (k :: α) : EuclideanSpace ℝ (Fin d) → ℝ)) :=
    fun m α hα =>
      HasWeakGradOn.mono hBV (hasWeakGradOn_of_hasWeakDerivOn fun k => (H m).D_step k α hα)
  -- Two families agree, entry by entry, on the ball.
  have hcoh : ∀ (α : List (Fin d)) (m₁ m₂ : ℕ), α.length ≤ m₁ → α.length ≤ m₂ →
      ((H m₁).D α : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict (Metric.ball c R)] ((H m₂).D α : EuclideanSpace ℝ (Fin d) → ℝ) := by
    intro α
    induction α with
    | nil =>
      intro m₁ m₂ _ _
      rw [(H m₁).D_nil, (H m₂).D_nil]
    | cons k α ih =>
      intro m₁ m₂ h1 h2
      have hl1 : α.length < m₁ := by simpa using h1
      have hl2 : α.length < m₂ := by simpa using h2
      have hg2' : HasWeakGradOn (Metric.ball c R)
          ((H m₁).D α : EuclideanSpace ℝ (Fin d) → ℝ)
          (fun j => ((H m₂).D (j :: α) : EuclideanSpace ℝ (Fin d) → ℝ)) :=
        HasWeakGradOn.congr_ae (hgradV m₂ α hl2) (ih m₂ m₁ hl2.le hl1.le) fun _ =>
          Filter.EventuallyEq.rfl
      exact hasWeakGradOn_unique_ae Metric.isOpen_ball measurableSet_ball (fun _ => hint _)
        (fun _ => hint _) (hgradV m₁ α hl1) hg2' k
  have hF0 : ((H ([] : List (Fin d)).length).D [] : EuclideanSpace ℝ (Fin d) → ℝ)
      = (u : EuclideanSpace ℝ (Fin d) → ℝ) := by
    simp only [List.length_nil]
    rw [(H 0).D_nil]
  refine ⟨fun α => ((H α.length).D α : EuclideanSpace ℝ (Fin d) → ℝ), fun α => ?_,
    fun α => hmemball _, hF0⟩
  simp only [List.length_cons]
  exact HasWeakGradOn.congr_ae (hgradV (α.length + 1) α (Nat.lt_succ_self _))
    (hcoh α (α.length + 1) α.length (Nat.le_succ _) le_rfl) fun _ => Filter.EventuallyEq.rfl

/-- **Weak derivatives up to order `m` give one family closed under differentiation as far as
`m`.** A single `EllipticPdes.Regularity.HasIteratedWeakDerivOn` at order `m` already assigns a
class to every list of directions, so the family is that assignment and nothing has to be
reconciled: `D_step` is the closure below order `m`, and membership at order `2` is inherited
from the region by restriction.

The unbounded statement needs uniqueness of the weak gradient because it receives one family per
order and has to identify the entries they share. Here there is one family, and the entries above
order `m` are carried along unconstrained, which is all the bounded ladder reads of them. -/
theorem exists_gradClosed_of_hasIteratedWeakDerivOn_le {V : Set (EuclideanSpace ℝ (Fin d))}
    (u : L2D V) {m : ℕ} (H : HasIteratedWeakDerivOn V m u)
    {c : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hBV : Metric.ball c R ⊆ V) :
    ∃ F : List (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ α, α.length < m → HasWeakGradOn (Metric.ball c R) (F α) (fun k => F (k :: α))) ∧
      (∀ α, MemLp (F α) 2 (volume.restrict (Metric.ball c R))) ∧
      F [] = (u : EuclideanSpace ℝ (Fin d) → ℝ) := by
  refine ⟨fun α => ((H.D α : EuclideanSpace ℝ (Fin d) → ℝ)), fun α hα => ?_,
    fun α => (Lp.memLp _).mono_measure (Measure.restrict_mono hBV le_rfl), by simp only [H.D_nil]⟩
  exact HasWeakGradOn.mono hBV (hasWeakGradOn_of_hasWeakDerivOn fun k => H.D_step k α hα)

end EllipticPdes.Regularity
