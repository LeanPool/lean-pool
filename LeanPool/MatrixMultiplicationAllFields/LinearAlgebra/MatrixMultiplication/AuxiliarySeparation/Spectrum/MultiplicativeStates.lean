/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.FixedPoint
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.NormalizedStates

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Multiplicative states obtained by normalizing translates of additive states. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open Set

variable {S : Type*} [CommSemiring S]

/-- Translate a state by multiplication, then normalize at the unit. -/
def normalizedTranslate (z : S) (f : S → ℝ) : S → ℝ :=
  fun x => f (z * x) / f z

theorem normalizedTranslate_continuousOn {K : Set (S → ℝ)} (z : S)
    (hz : ∀ f ∈ K, f z ≠ 0) :
    Continuous (fun f : K => normalizedTranslate z f.val) := by
  apply continuous_pi
  intro x
  exact ((continuous_apply (z * x)).comp continuous_subtype_val).div
    ((continuous_apply z).comp continuous_subtype_val) (fun f => hz f.val f.property)

/-- Functions satisfying a fixed multiplicative scaling relation at one semiring element. -/
def frozenConstraint (z : S) (c : ℝ) : Set (S → ℝ) :=
  {f | ∀ x, f (z * x) = c * f x}

/-- Intersect a family of candidate states with one multiplicative scaling constraint. -/
def frozenSlice (C : Set (S → ℝ)) (z : S) (c : ℝ) : Set (S → ℝ) :=
  C ∩ frozenConstraint z c

theorem frozenConstraint_isClosed (z : S) (c : ℝ) :
    IsClosed (frozenConstraint z c) := by
  unfold frozenConstraint
  simp only [ofPred_forall]
  exact isClosed_iInter fun x =>
    isClosed_eq (continuous_apply (z * x)) (continuous_const.mul (continuous_apply x))

theorem frozenSlice_isClosed {C : Set (S → ℝ)} (hC : IsClosed C) (z : S) (c : ℝ) :
    IsClosed (frozenSlice C z c) :=
  hC.inter (frozenConstraint_isClosed z c)

theorem frozenSlice_isCompact {C : Set (S → ℝ)} (hC : IsCompact C) (z : S) (c : ℝ) :
    IsCompact (frozenSlice C z c) :=
  hC.inter_right (frozenConstraint_isClosed z c)

theorem frozenConstraint_convex (z : S) (c : ℝ) :
    Convex ℝ (frozenConstraint z c) := by
  intro f hf g hg a b _ _ _ x
  change a * f (z * x) + b * g (z * x) = c * (a * f x + b * g x)
  rw [hf x, hg x]
  ring

theorem frozenSlice_convex {C : Set (S → ℝ)} (hC : Convex ℝ C) (z : S) (c : ℝ) :
    Convex ℝ (frozenSlice C z c) :=
  hC.inter (frozenConstraint_convex z c)

theorem normalizedTranslate_mem_frozenConstraint {z w : S} {c : ℝ} {f : S → ℝ}
    (hf : f ∈ frozenConstraint z c) :
    normalizedTranslate w f ∈ frozenConstraint z c := by
  intro x
  change f (w * (z * x)) / f w = c * (f (w * x) / f w)
  rw [show w * (z * x) = z * (w * x) by ac_rfl, hf (w * x)]
  ring

theorem frozenSlice_mapsTo_normalizedTranslate {C : Set (S → ℝ)} {z w : S} {c : ℝ}
    (hC : MapsTo (normalizedTranslate w) C C) :
    MapsTo (normalizedTranslate w) (frozenSlice C z c) (frozenSlice C z c) := by
  intro f hf
  exact ⟨hC hf.1, normalizedTranslate_mem_frozenConstraint hf.2⟩

theorem frozenConstraint_value {z : S} {c : ℝ} {f : S → ℝ}
    (hf : f ∈ frozenConstraint z c) (hf1 : f 1 = 1) : f z = c := by
  simpa only [mul_one, hf1] using hf 1

theorem frozenConstraint_normalizedTranslate_eq {z : S} {c : ℝ} {f : S → ℝ}
    (hf : f ∈ frozenConstraint z c) (hf1 : f 1 = 1) (hfz : f z ≠ 0) :
    normalizedTranslate z f = f := by
  funext x
  change f (z * x) / f z = f x
  rw [hf x, ← frozenConstraint_value hf hf1]
  exact mul_div_cancel_left₀ (f x) hfz

theorem normalizedTranslate_eq_mem_frozenConstraint {z : S} {f : S → ℝ}
    (hfz : f z ≠ 0) (hf : normalizedTranslate z f = f) :
    f ∈ frozenConstraint z (f z) := by
  intro x
  have hx : f (z * x) / f z = f x := congrFun hf x
  exact (div_eq_iff hfz).mp hx |>.trans (mul_comm _ _)

theorem normalizedTranslate_eq_nonzero {z : S} {f : S → ℝ}
    (hf1 : f 1 = 1) (hf : normalizedTranslate z f = f) : f z ≠ 0 := by
  intro hfz
  have hx := congrFun hf 1
  simp [normalizedTranslate, hfz, hf1] at hx

theorem normalizedTranslate_eq_mem_frozenConstraint_of_normalized {z : S} {f : S → ℝ}
    (hf1 : f 1 = 1) (hf : normalizedTranslate z f = f) :
    f ∈ frozenConstraint z (f z) :=
  normalizedTranslate_eq_mem_frozenConstraint (normalizedTranslate_eq_nonzero hf1 hf) hf

theorem normalizedTranslate_eq_mem_frozenSlice {C : Set (S → ℝ)} {z : S} {f : S → ℝ}
    (hfC : f ∈ C) (hf1 : f 1 = 1) (hf : normalizedTranslate z f = f) :
    f ∈ frozenSlice C z (f z) :=
  ⟨hfC, normalizedTranslate_eq_mem_frozenConstraint_of_normalized hf1 hf⟩

/-- Every finite collection of multiplication identities holds throughout a
nonempty compact convex subset that remains invariant under all translates. -/
theorem exists_finite_multiplicative_slice {K : Set (S → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (hKnorm : ∀ f ∈ K, f 1 = 1)
    (hKnonzero : ∀ f ∈ K, ∀ z : S, z ≠ 0 → f z ≠ 0)
    (hKmap : ∀ z : S, z ≠ 0 → MapsTo (normalizedTranslate z) K K)
    (t : Finset {z : S // z ≠ 0}) :
    ∃ C : Set (S → ℝ), C ⊆ K ∧ C.Nonempty ∧ IsCompact C ∧ Convex ℝ C ∧
      (∀ z : S, z ≠ 0 → MapsTo (normalizedTranslate z) C C) ∧
      ∀ f ∈ C, ∀ z ∈ t, ∀ x, f (z.val * x) = f z.val * f x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      exact ⟨K, Subset.rfl, hKne, hKcompact, hKconvex, hKmap, by simp⟩
  | @insert z t hzt ih =>
      obtain ⟨C, hCK, hCne, hCcompact, hCconvex, hCmap, hCt⟩ := ih
      let P : C → C := fun f =>
        ⟨normalizedTranslate z.val f.val, hCmap z.val z.property f.property⟩
      have hP : Continuous P := by
        apply Continuous.subtype_mk
        exact normalizedTranslate_continuousOn z.val
          (fun f hf => hKnonzero f (hCK hf) z.val z.property)
      obtain ⟨g, hg⟩ := compact_convex_fixedPoint_of_continuous
        hCcompact hCconvex hCne P hP
      have hg' : normalizedTranslate z.val g.val = g.val := congrArg Subtype.val hg
      let c : ℝ := g.val z.val
      let D := frozenSlice C z.val c
      have hDC : D ⊆ C := fun _ hf => hf.1
      have hDK : D ⊆ K := hDC.trans hCK
      refine ⟨D, hDK, ?_, frozenSlice_isCompact hCcompact z.val c,
        frozenSlice_convex hCconvex z.val c, ?_, ?_⟩
      · exact ⟨g.val, normalizedTranslate_eq_mem_frozenSlice g.property
          (hKnorm g.val (hCK g.property)) hg'⟩
      · intro w hw
        exact frozenSlice_mapsTo_normalizedTranslate (hCmap w hw)
      · intro f hf w hw x
        rcases Finset.mem_insert.mp hw with rfl | hwt
        · have hfc : f w.val = c := frozenConstraint_value hf.2 (hKnorm f (hDK hf))
          rw [hfc]
          exact hf.2 x
        · exact hCt f (hDC hf) w hwt x

/-- A compact convex normalized state space invariant under multiplication
translates contains a multiplicative state. Frozen eigenvalue slices preserve
convexity at each finite fixed-point step. -/
theorem exists_multiplicative_of_invariant_states {K : Set (S → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (hKnorm : ∀ f ∈ K, f 1 = 1) (hKzero : ∀ f ∈ K, f 0 = 0)
    (hKnonzero : ∀ f ∈ K, ∀ z : S, z ≠ 0 → f z ≠ 0)
    (hKmap : ∀ z : S, z ≠ 0 → MapsTo (normalizedTranslate z) K K) :
    ∃ f ∈ K, ∀ x y, f (x * y) = f x * f y := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  let F : {z : S // z ≠ 0} → Set K :=
    fun z => {f | ∀ x, f.val (z.val * x) = f.val z.val * f.val x}
  have hFclosed (z : {z : S // z ≠ 0}) : IsClosed (F z) := by
    change IsClosed {f : K | ∀ x, f.val (z.val * x) = f.val z.val * f.val x}
    simp only [ofPred_forall]
    exact isClosed_iInter fun x =>
      isClosed_eq ((continuous_apply (z.val * x)).comp continuous_subtype_val)
        (((continuous_apply z.val).comp continuous_subtype_val).mul
          ((continuous_apply x).comp continuous_subtype_val))
  have hFfinite (t : Finset {z : S // z ≠ 0}) : (⋂ z ∈ t, F z).Nonempty := by
    obtain ⟨C, hCK, hCne, _, _, _, hCt⟩ := exists_finite_multiplicative_slice
      hKcompact hKconvex hKne hKnorm hKnonzero hKmap t
    obtain ⟨f, hf⟩ := hCne
    refine ⟨⟨f, hCK hf⟩, ?_⟩
    simp only [mem_iInter]
    intro z hz
    exact hCt f hf z hz
  obtain ⟨f, hf⟩ := CompactSpace.iInter_nonempty hFclosed hFfinite
  refine ⟨f.val, f.property, fun x y => ?_⟩
  by_cases hx : x = 0
  · simp [hx, hKzero f.val f.property]
  · exact mem_iInter.mp hf ⟨x, hx⟩ y

/-- Appendix A.2 for a ranked restriction semiring: once the preliminary
normalized state set is nonempty, it contains a multiplicative state. -/
theorem normalizedStates_exists_multiplicative [Preorder S]
    (R : S → ℕ) (d : S) (k : ℝ)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hmulmono : ∀ z x y : S, x ≤ y → z * x ≤ z * y)
    (hdom : ∀ z x : S, z * x ≤ (R x : S) * z)
    (hne : (normalizedStates (fun x => (R x : ℝ)) d k).Nonempty) :
    ∃ f ∈ normalizedStates (fun x => (R x : ℝ)) d k,
      ∀ x y, f (x * y) = f x * f y := by
  apply exists_multiplicative_of_invariant_states
    (normalizedStates_isCompact _ d k) (normalizedStates_convex _ d k) hne
  · exact fun _ hf => hf.2.1
  · exact fun _ hf => state_zero hf
  · intro f hf z hz
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (state_one_le hf (hunit z hz)))
  · intro z hz f hf
    exact state_rescale hf z (hunit z hz) (hmulmono z) (hdom z)

/-- The multiplicative state as a normalized monotone semiring homomorphism,
with the original rank bounds and detector inequality preserved. -/
theorem exists_monotone_semiringHom_of_normalizedStates [Preorder S]
    (R : S → ℕ) (d : S) (k : ℝ)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hmulmono : ∀ z x y : S, x ≤ y → z * x ≤ z * y)
    (hdom : ∀ z x : S, z * x ≤ (R x : S) * z)
    (hne : (normalizedStates (fun x => (R x : ℝ)) d k).Nonempty) :
    ∃ χ : S →+* ℝ, Monotone χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ R x) ∧ k ≤ χ d := by
  obtain ⟨f, hf, hfmul⟩ :=
    normalizedStates_exists_multiplicative R d k hunit hmulmono hdom hne
  let χ : S →+* ℝ :=
    { toFun := f
      map_zero' := state_zero hf
      map_one' := hf.2.1
      map_add' := hf.2.2.1
      map_mul' := hfmul }
  refine ⟨χ, ?_, hf.1, ?_⟩
  · intro x y hxy
    exact hf.2.2.2.1 x y hxy
  · simpa only [χ, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      mul_one, hf.2.1] using hf.2.2.2.2 1

end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
