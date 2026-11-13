/-
Copyright (c) 2026 Raúl E. Pariente-Martín, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raúl E. Pariente-Martín, Pedro Tradacete
-/

module

public import LeanPool.FBLOrderContinuity.Model
public import LeanPool.FBLOrderContinuity.BanLat.Operators.OrderContinuous
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.ModelTheory.Substructures



/-!
# Order continuity and algebraic witnesses

This module formalizes the order-theoretic part of Sections 1–3. `DecreasesToZero`
expresses decrease to a greatest lower bound of zero, and `SigmaOrderContinuous` is
the sequential version of BanLat's order-continuity predicate. The countable supremum
property of `Free p E` reduces order continuity to tests on sequences in `FVL E`.

The main results are `separable_reduction`, `injectivity`, `noncompact_minima`, and
`necessary`. They reduce failure of order continuity to separable Banach-space ideals
and give explicit witnesses. `intro_infty` proves the complete endpoint criterion:
the original operator is zero or bounded below.

The final part treats vector spaces without a norm through `AlgebraicFVL`, proves
`fvl_characterization`, and identifies that model with BanLat's `FVL` when a norm is
available. Banach-space ideals here concern Hahn–Banach extension of dual functionals.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal Topology
open Filter Set
universe u v w
namespace FBLOrderContinuousLH

/-- Section 2: decreasing nets with greatest lower bound zero. -/
def DecreasesToZero {ι : Type w} {X : Type u} [Preorder ι] [Preorder X] [Zero X]
    (x : ι → X) : Prop := Antitone x ∧ IsGLB (Set.range x) 0

/-- Section 2: the sequential order-continuity test for positive maps. -/
def SigmaOrderContinuous {X : Type u} {Y : Type v}
    [Preorder X] [Zero X] [Preorder Y] [Zero Y] (S : X → Y) : Prop :=
  ∀ x : ℕ → X, DecreasesToZero x → DecreasesToZero (fun n => S (x n))

/-- Section 2: the countable supremum property, including arbitrary subsets. -/
def CountableSupProperty (X : Type u) [Preorder X] : Prop :=
  ∀ (A : Set X) (a : X), IsLUB A a →
    ∃ B : Set X, B ⊆ A ∧ B.Countable ∧ IsLUB B a

/-- A positive operator's decreasing-net test agrees with BanLat's order convergence API. -/
theorem orderContinuous_iff_decreasing {X : Type u} {Y : Type v}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (S : X →ₗ[ℝ] Y) (hS : ∀ x, 0 ≤ x → 0 ≤ S x) :
    IsOrderContinuousOp S ↔
      ∀ (ι : Type u) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
        (x : ι → X), DecreasesToZero x → DecreasesToZero (fun i => S (x i)) := by
  have hmono : Monotone S := Positive.monotone_iff.mpr hS
  constructor
  · intro h ι _ _ _ x hx
    have hc := h (orderConvergesTo_of_antitone_isGLB hx.1 hx.2)
    exact ⟨hmono.comp_antitone hx.1,
      ⟨by rintro _ ⟨i, rfl⟩; exact hS _ (hx.2.1 ⟨i, rfl⟩),
       fun _ hb => by simpa only [map_zero] using hc.forall_le (fun i => hb ⟨i, rfl⟩)⟩⟩
  · intro h ι _ _ _ x a hx
    rcases hx with ⟨κ, hκ, hdκ, hnκ, r, hr, hrpos, hrglb, hevent⟩
    let := hκ
    let := hdκ
    let := hnκ
    obtain ⟨ha, hb⟩ := h κ r ⟨hr, hrglb⟩
    rcases orderConvergesTo_of_antitone_isGLB ha hb with
      ⟨τ, hτ, hdτ, hnτ, s, hs, hspos, hsglb, hsevent⟩
    refine ⟨τ, hτ, hdτ, hnτ, s, hs, hspos, hsglb, fun k => ?_⟩
    obtain ⟨j, hj⟩ := (hsevent k).exists
    exact (hevent j).mono fun i hi => by
      calc
        |S (x i) - S a| = |S (x i - a)| := by rw [map_sub]
        _ ≤ S |x i - a| := Positive.abs_le_map_abs hS _
        _ ≤ S (r j) := hmono hi
        _ ≤ |S (r j) - 0| := by simpa only [sub_zero] using le_abs_self (S (r j))
        _ ≤ s k := hj

/-- Order-continuous positive operators preserve decreasing sequences, in any domain universe. -/
theorem orderContinuous_sigmaOrderContinuous {X : Type u} {Y : Type v}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (S : X →ₗ[ℝ] Y) (hS : ∀ x, 0 ≤ x → 0 ≤ S x) (h : IsOrderContinuousOp S) :
    SigmaOrderContinuous S := by
  intro x hx
  have hrange : Set.range (fun n : ULift.{u} ℕ => x n.down) = Set.range x :=
    ULift.down_surjective.range_comp x
  have hc := (orderContinuous_iff_decreasing S hS).mp h (ULift.{u} ℕ)
    (fun n => x n.down) ⟨fun _ _ h => hx.1 h, hrange.symm ▸ hx.2⟩
  exact ⟨fun _ _ h => hc.1 (show (ULift.up _ : ULift.{u} ℕ) ≤ ULift.up _ from h),
    (ULift.down_surjective.range_comp (fun n => S (x n))) ▸ hc.2⟩

/-- Proposition 2.2 (`prop:csp-operator`): for a positive linear map whose domain has
the countable supremum property, preservation of decreasing order-null sequences is
equivalent to order continuity for arbitrary directed nets. -/
theorem csp_operator {X : Type u} {Y : Type v}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (hX : CountableSupProperty X) (S : X →ₗ[ℝ] Y)
    (hS : ∀ x, 0 ≤ x → 0 ≤ S x) :
    IsOrderContinuousOp S ↔ SigmaOrderContinuous S := by
  rw [orderContinuous_iff_decreasing S hS]
  constructor
  · intro h x hx
    have hrange : Set.range (fun n : ULift.{u} ℕ => x n.down) = Set.range x :=
      (ULift.down_surjective.range_comp x)
    have hc := h (ULift.{u} ℕ) (fun n => x n.down)
      ⟨fun _ _ h => hx.1 h, hrange.symm ▸ hx.2⟩
    exact ⟨fun _ _ h => hc.1 (show (ULift.up _ : ULift.{u} ℕ) ≤ ULift.up _ from h),
      (ULift.down_surjective.range_comp (fun n => S (x n))) ▸ hc.2⟩
  · intro h ι _ _ _ x hx
    classical
    obtain ⟨B, hB, hBc, hBlub⟩ := hX (-(Set.range x)) 0 (by simpa using hx.2.neg)
    let i₀ : ι := Classical.choice inferInstance
    obtain ⟨b, hb⟩ := (hBc.insert (-x i₀)).exists_eq_range (Set.insert_nonempty _ _)
    have hbi (n : ℕ) : ∃ i, x i = -b n := by
      change -b n ∈ Set.range x
      apply Set.mem_neg.mp
      have hn : b n ∈ insert (-x i₀) B := hb.symm ▸ Set.mem_range_self n
      rcases hn with hn | hn
      · simp only [hn, Set.mem_neg, neg_neg, Set.mem_range_self]
      · exact hB hn
    choose a ha using hbi
    choose upper hleft hright using (fun i j : ι => directed_of (· ≤ ·) i j)
    let β : ℕ → ι := Nat.rec i₀ (fun n i => upper i (a n))
    have hβ : Monotone β := monotone_nat_of_le_succ fun n => hleft (β n) (a n)
    have haβ (n : ℕ) : a n ≤ β (n + 1) := hright (β n) (a n)
    have hxβ : DecreasesToZero (fun n => x (β n)) := by
      refine ⟨hx.1.comp_monotone hβ, ⟨?_, ?_⟩⟩
      · rintro _ ⟨n, rfl⟩
        exact hx.2.1 ⟨β n, rfl⟩
      · intro z hz
        suffices 0 ≤ -z by simpa using this
        apply hBlub.2
        intro y hy
        obtain ⟨n, rfl⟩ := hb ▸ Set.mem_insert_of_mem _ hy
        have hz' : z ≤ -b n := (hz ⟨n + 1, rfl⟩).trans ((hx.1 (haβ n)).trans_eq (ha n))
        exact le_neg.mpr hz'
    exact ⟨(Positive.monotone_iff.mpr hS).comp_antitone hx.1,
      ⟨by rintro _ ⟨i, rfl⟩; exact hS _ (hx.2.1 ⟨i, rfl⟩),
        fun z hz => (h _ hxβ).2.2 (by rintro _ ⟨n, rfl⟩; exact hz ⟨β n, rfl⟩)⟩⟩

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem finite_positive_lower_bound {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ s, 0 < r i) : ∃ δ > 0, ∀ i ∈ s, δ ≤ r i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨δ, hδ, hle⟩ := ih (fun j hj => hr j (Finset.mem_insert_of_mem hj))
    refine ⟨min (r i) δ, lt_min (hr i (Finset.mem_insert_self _ _)) hδ, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hle j hj)

private theorem weakDual_neighborhood_finite (φ : WeakDual ℝ E)
    (U : Set (WeakDual ℝ E)) (hU : U ∈ 𝓝 φ) :
    ∃ (s : Finset E) (δ : ℝ), 0 < δ ∧
      ∀ ψ : WeakDual ℝ E, (∀ x ∈ s, |ψ x - φ x| < δ) → ψ ∈ U := by
  classical
  have hEmb : Topology.IsEmbedding (fun θ : WeakDual ℝ E => (θ : E → ℝ)) :=
    WeakBilin.isEmbedding (by
      intro a b hab
      apply ContinuousLinearMap.ext
      intro x
      simpa only [topDualPairing_apply] using congrArg (fun l : E →ₗ[ℝ] ℝ => l x) hab)
  rw [hEmb.isInducing.nhds_eq_comap φ] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
  rw [nhds_pi] at hV
  obtain ⟨⟨s, r⟩, ⟨hs, hr⟩, hsub⟩ :=
    (Filter.hasBasis_pi (fun x : E => Metric.nhds_basis_ball (x := φ x))).mem_iff.mp hV
  obtain ⟨δ, hδ, hle⟩ := finite_positive_lower_bound hs.toFinset r
    (fun x hx => hr x (hs.mem_toFinset.mp hx))
  refine ⟨hs.toFinset, δ, hδ, fun ψ hψ => hVU (hsub ?_)⟩
  intro x hx
  exact (show |ψ x - φ x| < r x from
    (hψ x (hs.mem_toFinset.mpr hx)).trans_le (hle x (hs.mem_toFinset.mpr hx)))

private theorem positive_free_certificate (p : Exponent) (f : Free p E) (hf : 0 < f) :
    ∃ (φ : Dual E) (n m k : ℕ) (x : Fin n → E), ‖φ‖ ≤ 1 / 3 ∧
      (∀ i, ‖x i‖ ≤ m) ∧
      ∀ ψ : Dual E, ‖ψ‖ ≤ 1 →
        (∀ i, |ψ (x i) - φ (x i)| < 1 / ((k : ℝ) + 1)) → 0 < f ψ := by
  classical
  obtain ⟨θ, hθ⟩ : ∃ θ : Dual E, 0 < f θ := by
    by_contra! h
    exact hf.not_ge ((free_le_iff p _ _).mpr h)
  let a : ℝ := 1 / (3 * (‖θ‖ + 1))
  have ha : 0 < a := by dsimp [a]; positivity
  let φ := a • θ
  have hφnorm : ‖φ‖ ≤ 1 / 3 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    dsimp [a]
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    linarith
  have hφ : 0 < f φ := by rw [show f φ = a * f θ from f.1.2.1 a ha.le θ]; positivity
  have hev : {ψ : WeakDual ℝ E | 0 < f ψ.toStrongDual} ∈
      𝓝[{ψ | ‖ψ.toStrongDual‖ ≤ 1}] (StrongDual.toWeakDual φ) :=
    (weakStar_continuous_bounded p f 1 _ (by change ‖φ‖ ≤ 1; linarith)).preimage_mem_nhdsWithin
      (Ioi_mem_nhds hφ)
  obtain ⟨U, hU, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hev
  obtain ⟨s, δ, hδ, hcert⟩ := weakDual_neighborhood_finite (StrongDual.toWeakDual φ) U hU
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  let x : Fin (Fintype.card s) → E := fun i => ((Fintype.equivFin s).symm i : E)
  obtain ⟨C, hC⟩ := (Set.finite_range x).isBounded.exists_norm_le
  obtain ⟨m, hm⟩ := exists_nat_gt C
  refine ⟨φ, Fintype.card s, m, k, x, hφnorm,
    fun i => (hC _ (Set.mem_range_self i)).trans hm.le, fun ψ hψ hclose => ?_⟩
  apply hsub
  refine ⟨hcert (StrongDual.toWeakDual ψ) ?_, hψ⟩
  intro y hy
  have hi := hclose ((Fintype.equivFin s) ⟨y, hy⟩)
  simpa only [x, Equiv.symm_apply_apply, StrongDual.toWeakDual_apply] using hi.trans hk

private theorem finite_color_triple {C : Type*} [Finite C] (c : ℕ → ℕ → C) :
    ∃ i j k, i < j ∧ j < k ∧ c i j = c i k ∧ c k i = c k j := by
  let U := hyperfilter ℕ
  have hcol (i : ℕ) : ∃ a, ∀ᶠ j in U, c j i = a :=
    Ultrafilter.eventually_exists_iff.mp (Eventually.of_forall (fun j => ⟨c j i, rfl⟩))
  choose d hd using hcol
  obtain ⟨a, ha⟩ : ∃ a, ∀ᶠ i in U, d i = a :=
    Ultrafilter.eventually_exists_iff.mp (Eventually.of_forall (fun i => ⟨d i, rfl⟩))
  obtain ⟨i, hi⟩ := ha.exists
  obtain ⟨b, hb⟩ : ∃ b, ∀ᶠ j in U, c i j = b :=
    Ultrafilter.eventually_exists_iff.mp (Eventually.of_forall (fun j => ⟨c i j, rfl⟩))
  have hlarge (n : ℕ) : ∀ᶠ j in U, n < j :=
    Nat.hyperfilter_le_atTop (eventually_gt_atTop n)
  obtain ⟨j, hj, hij, hlargej⟩ := (ha.and (hb.and (hlarge i))).exists
  obtain ⟨k, hik, hki, hkj, hlargek⟩ :=
    (hb.and ((hd i).and ((hd j).and (hlarge j)))).exists
  exact ⟨i, j, k, hlargej, hlargek, hij.trans hik.symm,
    hki.trans (hi.trans (hj.symm.trans hkj.symm))⟩

private theorem bounded_matrix_triple {n : ℕ} (a : ℕ → ℕ → (Fin n → ℝ))
    {C δ : ℝ} (hC : 0 ≤ C) (ha : ∀ i j t, |a i j t| ≤ C) (hδ : 0 < δ) :
    ∃ i j k, i < j ∧ j < k ∧
      (∀ t, |a i j t - a i k t| < δ) ∧ (∀ t, |a k i t - a k j t| < δ) := by
  classical
  have hmem (i j : ℕ) : a i j ∈ Metric.closedBall (0 : Fin n → ℝ) C := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hC]
    exact ha i j
  obtain ⟨s, hs, hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_closedBall (0 : Fin n → ℝ) C).totallyBounded (δ / 2) (by positivity)
  have hchoose (i j : ℕ) : ∃ b ∈ s, dist (a i j) b < δ / 2 := by
    obtain ⟨b, hb, hdist⟩ := Set.mem_iUnion₂.mp (hcover (hmem i j))
    exact ⟨b, hb, hdist⟩
  choose b hb hdist using hchoose
  let := hs.fintype
  have hclose (i j k l : ℕ) (heq : b i j = b k l) :
      ∀ t, |a i j t - a k l t| < δ := by
    have hd : dist (a i j) (a k l) < δ := by
      have ht := dist_triangle (a i j) (b i j) (a k l)
      rw [heq, dist_comm (b k l) (a k l)] at ht
      have hdij := hdist i j
      rw [heq] at hdij
      linarith [hdist k l]
    intro t
    exact (show |a i j t - a k l t| ≤ dist (a i j) (a k l) from
      norm_le_pi_norm (a i j - a k l) t).trans_lt hd
  obtain ⟨i, j, k, hij, hjk, hrow, hcol⟩ :=
    finite_color_triple (fun i j => (⟨b i j, hb i j⟩ : s))
  exact ⟨i, j, k, hij, hjk, hclose i j i k (congrArg Subtype.val hrow),
    hclose k i k j (congrArg Subtype.val hcol)⟩

/-- Section 2, the disjoint-family consequence used to obtain the countable supremum property. -/
theorem disjoint_positive_countable (p : Exponent) (A : Set (Free p E))
    (hpos : ∀ f ∈ A, 0 < f) (hdisj : A.Pairwise (fun f g => f ⊓ g = 0)) :
    A.Countable := by
  classical
  let B (n m k : ℕ) : Set (Free p E) := {f | f ∈ A ∧
    ∃ (φ : Dual E) (x : Fin n → E), ‖φ‖ ≤ 1 / 3 ∧ (∀ i, ‖x i‖ ≤ m) ∧
      ∀ ψ : Dual E, ‖ψ‖ ≤ 1 →
        (∀ i, |ψ (x i) - φ (x i)| < 1 / ((k : ℝ) + 1)) → 0 < f ψ}
  have hfinite (n m k : ℕ) : (B n m k).Finite := by
    by_contra hfin
    let a := Set.Infinite.natEmbedding (B n m k) hfin
    choose φ x hφ hx hcert using (fun i => (a i).2.2)
    obtain ⟨i, j, l, hij, hjl, hrow, hcol⟩ := bounded_matrix_triple
      (fun i j t => φ j (x i t)) (Nat.cast_nonneg m)
      (fun i j t => ((φ j).le_opNorm (x i t)).trans (by
        have := hx i t
        have := hφ j
        nlinarith [norm_nonneg (φ j), norm_nonneg (x i t)]))
      (show 0 < 1 / ((k : ℝ) + 1) by positivity)
    let ψ : Dual E := φ i - φ j + φ l
    have hψ : ‖ψ‖ ≤ 1 := by
      have hnorm := (norm_add_le (φ i - φ j) (φ l)).trans
        (add_le_add (norm_sub_le (φ i) (φ j)) le_rfl)
      dsimp [ψ]
      linarith [hφ i, hφ j, hφ l]
    have hi : 0 < (a i).1 ψ := hcert i ψ hψ (fun t => by
      have heq : ψ (x i t) - φ i (x i t) = -(φ j (x i t) - φ l (x i t)) := by
        simp only [ψ, sub_apply, add_apply]
        ring
      rw [heq, abs_neg]
      exact hrow t)
    have hl : 0 < (a l).1 ψ := hcert l ψ hψ (fun t => by
      have heq : ψ (x l t) - φ l (x l t) = φ i (x l t) - φ j (x l t) := by
        simp only [ψ, sub_apply, add_apply]
        ring
      rw [heq]
      exact hcol t)
    have hne : (a i).1 ≠ (a l).1 := fun he => (ne_of_lt (hij.trans hjl))
      (a.injective (Subtype.ext he))
    have hzero := congrArg (fun f : Free p E => f ψ)
      (hdisj (a i).2.1 (a l).2.1 hne)
    change min ((a i).1 ψ) ((a l).1 ψ) = 0 at hzero
    exact (lt_min hi hl).ne' hzero
  apply (Set.countable_iUnion fun n => Set.countable_iUnion fun m =>
    Set.countable_iUnion fun k => (hfinite n m k).countable).mono
  intro f hf
  obtain ⟨φ, n, m, k, x, hφ, hx, hcert⟩ := positive_free_certificate p f (hpos f hf)
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨m,
    Set.mem_iUnion.mpr ⟨k, hf, φ, x, hφ, hx, hcert⟩⟩⟩

private theorem countable_disjoint_detection (p : Exponent)
    (C : Set (Free p E)) (hC : ∀ f ∈ C, 0 ≤ f) :
    ∃ B : Set (Free p E), B ⊆ C ∧ B.Countable ∧
      ∀ g : Free p E, 0 ≤ g → (∀ b ∈ B, g ⊓ b = 0) → ∀ c ∈ C, g ⊓ c = 0 := by
  classical
  let L : Set (Free p E) := {f | 0 < f ∧ ∃ c ∈ C, f ≤ c}
  let Q : Set (Set (Free p E)) := {D | D ⊆ L ∧ D.Pairwise (fun f g => f ⊓ g = 0)}
  obtain ⟨D, hD, hmax⟩ := zorn_subset Q (by
    intro chain hchain hc
    refine ⟨⋃₀ chain, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro f ⟨s, hs, hfs⟩
      exact (hchain hs).1 hfs
    · rintro f ⟨s, hs, hfs⟩ g ⟨t, ht, hgt⟩ hne
      rcases hc.total hs ht with hst | hts
      · exact (hchain ht).2 (hst hfs) hgt hne
      · exact (hchain hs).2 hfs (hts hgt) hne)
  have hDc := disjoint_positive_countable p D (fun f hf => (hD.1 hf).1) hD.2
  let := hDc.to_subtype
  choose v hv hle using (fun y : D => (hD.1 y.2).2)
  refine ⟨Set.range v, ?_, Set.countable_range v, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact hv y
  · intro g hg hgb c hc
    let z := g ⊓ c
    have hzpos : 0 ≤ z := le_inf hg (hC c hc)
    apply le_antisymm _ hzpos
    by_contra hzne
    have hzlt : 0 < z := lt_of_le_of_ne hzpos (fun he => hzne (le_of_eq he.symm))
    have hzL : z ∈ L := ⟨hzlt, c, hc, inf_le_right⟩
    have hzy (y : Free p E) (hy : y ∈ D) : z ⊓ y = 0 := by
      have hypos := (hD.1 hy).1.le
      exact le_antisymm ((inf_le_inf (show z ≤ g from inf_le_left) (hle ⟨y, hy⟩)).trans_eq
        (hgb (v ⟨y, hy⟩) (Set.mem_range_self _))) (le_inf hzpos hypos)
    have hinsert : insert z D ∈ Q := by
      refine ⟨Set.insert_subset_iff.mpr ⟨hzL, hD.1⟩, ?_⟩
      exact Set.pairwise_insert.mpr ⟨hD.2, fun y hy _ =>
        ⟨hzy y hy, (inf_comm y z).trans (hzy y hy)⟩⟩
    have hzD : z ∈ D := hmax hinsert (Set.subset_insert _ _) (Set.mem_insert _ _)
    exact hzlt.ne' (by simpa only [inf_idem] using hzy z hzD)

private theorem countable_lower_approximation (p : Exponent)
    (A : Set (Free p E)) (a : Free p E) (ha : 0 ≤ a) (hA : IsLUB A a)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ∃ B : Set (Free p E), B ⊆ A ∧ B.Countable ∧
      ∀ b, 0 ≤ b → b ∈ upperBounds B → r • a ≤ b := by
  classical
  let C := (fun u : Free p E => (u - r • a)⁺) '' A
  obtain ⟨D, hDC, hDc, hdet⟩ := countable_disjoint_detection p C
    (by rintro _ ⟨u, _, rfl⟩; exact posPart_nonneg _)
  let := hDc.to_subtype
  choose v hv hveq using (fun d : D => hDC d.2)
  refine ⟨Set.range v, ?_, Set.countable_range v, ?_⟩
  · rintro _ ⟨d, rfl⟩
    exact hv d
  · intro b hb hbB
    let g := (r • a - b)⁺ ⊓ ((1 - r) • a)
    have hg : 0 ≤ g := le_inf (posPart_nonneg _) (smul_nonneg (by linarith) ha)
    have hgd (d : D) : g ⊓ d.1 = 0 := by
      rw [← hveq d]
      apply le_antisymm _ (le_inf hg (posPart_nonneg _))
      have hbound := inf_le_inf (show g ≤ (r • a - b)⁺ from inf_le_left)
        (posPart_mono (sub_le_sub_right (hbB (Set.mem_range_self d)) (r • a)))
      apply hbound.trans_eq
      simpa only [negPart_def, neg_sub, posPart_def] using
        posPart_inf_negPart_eq_zero (r • a - b)
    have hgu (u : Free p E) (hu : u ∈ A) : g ⊓ (u - r • a)⁺ = 0 :=
      hdet g hg (fun d hd => hgd ⟨d, hd⟩) _ ⟨u, hu, rfl⟩
    have hupper : a - g ∈ upperBounds A := by
      intro u hu
      apply (free_le_iff p _ _).mpr
      intro φ
      have hua := (free_le_iff p _ _).mp (hA.1 hu) φ
      have hgφ := (free_le_iff p _ _).mp hg φ
      have hgbound := (free_le_iff p _ _).mp (show g ≤ (1 - r) • a from inf_le_right) φ
      have hz := congrArg (fun f : Free p E => f φ) (hgu u hu)
      change min (g φ) (max (u φ - r * a φ) 0) = 0 at hz
      change g φ ≤ (1 - r) * a φ at hgbound
      change u φ ≤ a φ - g φ
      by_cases hzero : g φ = 0
      · simpa only [hzero, sub_zero] using hua
      have hgp : 0 < g φ := lt_of_le_of_ne hgφ (Ne.symm hzero)
      have hur : u φ ≤ r * a φ := by
        by_contra! hlt
        exact (lt_min hgp (lt_max_of_lt_left (by linarith))).ne' hz
      nlinarith
    have hgzero : g ≤ 0 := by
      have h := hA.2 hupper
      exact sub_nonpos.mp (by simpa using sub_le_sub_left h a)
    apply (free_le_iff p _ _).mpr
    intro φ
    have hgz := (free_le_iff p _ _).mp hgzero φ
    have haφ := (free_le_iff p _ _).mp ha φ
    have hbφ := (free_le_iff p _ _).mp hb φ
    change 0 ≤ a φ at haφ
    change 0 ≤ b φ at hbφ
    change r * a φ ≤ b φ
    change min (max (r * a φ - b φ) 0) ((1 - r) * a φ) ≤ 0 at hgz
    by_contra! hlt
    have hap : 0 < a φ := by nlinarith
    exact (lt_min (lt_max_of_lt_left (by linarith)) (mul_pos (by linarith) hap)).not_ge hgz

private theorem countable_lub_positive (p : Exponent)
    (A : Set (Free p E)) (a : Free p E) (hA : IsLUB A a) (hne : A.Nonempty)
    (hpos : ∀ u ∈ A, 0 ≤ u) :
    ∃ B : Set (Free p E), B ⊆ A ∧ B.Countable ∧ IsLUB B a := by
  classical
  obtain ⟨a₀, ha₀⟩ := hne
  have ha : 0 ≤ a := (hpos a₀ ha₀).trans (hA.1 ha₀)
  let r (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 ≤ r n := by
    dsimp [r]
    have h : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr
      (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  have hr1 (n : ℕ) : r n < 1 := by
    dsimp [r]
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose B hBA hBc hB using
    (fun n => countable_lower_approximation p A a ha hA (r n) (hr n) (hr1 n))
  refine ⟨insert a₀ (⋃ n, B n), Set.insert_subset_iff.mpr ⟨ha₀, Set.iUnion_subset hBA⟩,
    (Set.countable_iUnion hBc).insert a₀, ⟨fun u hu => hA.1 ?_, ?_⟩⟩
  · rcases hu with rfl | hu
    · exact ha₀
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hu
      exact hBA n hn
  · intro b hb
    have hbpos : 0 ≤ b := (hpos a₀ ha₀).trans (hb (Set.mem_insert _ _))
    have hbound (n : ℕ) : r n • a ≤ b := hB n b hbpos
      (fun u hu => hb (Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨n, hu⟩)))
    have hrconv : Tendsto r atTop (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact le_of_tendsto' (by simpa only [one_smul] using hrconv.smul_const a) hbound

/-- Lemma 2.1 (`lem:csp`): every free p-convex lattice over a Banach space has the
countable supremum property. The proof first shows that pairwise disjoint families of
strictly positive elements are countable, then extracts a countable set with the same supremum. -/
theorem csp (p : Exponent) : CountableSupProperty (Free p E) := by
  classical
  intro A a hA
  by_cases hne : A.Nonempty
  · obtain ⟨a₀, ha₀⟩ := hne
    let P := (fun u : Free p E => u ⊔ a₀ - a₀) '' A
    have hPpos : ∀ u ∈ P, 0 ≤ u := by
      rintro _ ⟨u, _, rfl⟩
      exact sub_nonneg.mpr le_sup_right
    have hPlub : IsLUB P (a - a₀) := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨u, hu, rfl⟩
        exact sub_le_sub_right (sup_le (hA.1 hu) (hA.1 ha₀)) a₀
      · intro b hb
        apply sub_le_iff_le_add.mpr
        apply hA.2
        intro u hu
        exact le_sup_left.trans (sub_le_iff_le_add.mp (hb ⟨u, hu, rfl⟩))
    obtain ⟨D, hDP, hDc, hDlub⟩ := countable_lub_positive p P (a - a₀) hPlub
      ⟨a₀ ⊔ a₀ - a₀, a₀, ha₀, rfl⟩ hPpos
    let := hDc.to_subtype
    choose v hv hveq using (fun d : D => hDP d.2)
    refine ⟨insert a₀ (Set.range v), ?_, (Set.countable_range v).insert a₀, ⟨?_, ?_⟩⟩
    · rintro u (rfl | ⟨d, rfl⟩)
      · exact ha₀
      · exact hv d
    · rintro u (rfl | ⟨d, rfl⟩)
      · exact hA.1 ha₀
      · exact hA.1 (hv d)
    · intro b hb
      have hbase : a₀ ≤ b := hb (Set.mem_insert _ _)
      have hDupper : b - a₀ ∈ upperBounds D := by
        intro d hd
        exact (hveq ⟨d, hd⟩).symm.trans_le (sub_le_sub_right
          (sup_le (hb (Set.mem_insert_of_mem _ (Set.mem_range_self ⟨d, hd⟩))) hbase) a₀)
      exact (sub_le_sub_iff_right a₀).mp (hDlub.2 hDupper)
  · exact ⟨A, Set.Subset.rfl, (Set.not_nonempty_iff_eq_empty.mp hne) ▸ Set.countable_empty, hA⟩

/-- Lemma 2.3 (`lem:sigma-order-continuity`): a positive linear map from `Free p E`
is order continuous exactly when it preserves decreasing order-null sequences. The
countable supremum property supplies the reduction; boundedness of the map is unnecessary. -/
theorem sigma_order_continuity (p : Exponent)
    {Y : Type v} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [BanachLattice Y] (S : Free p E →ₗ[ℝ] Y) (hS : ∀ x, 0 ≤ x → 0 ≤ S x) :
    IsOrderContinuousOp S ↔ SigmaOrderContinuous S := csp_operator (csp p) S hS

private theorem positive_fvl_approximation (p : Exponent) (f : Free p F) (hf : 0 ≤ f)
    {ε : ℝ} (hε : 0 < ε) : ∃ g : FVL F, 0 ≤ g ∧ ‖ofFVL p g - f‖ < ε := by
  obtain ⟨g, hg⟩ := (denseRange_ofFVL p).exists_dist_lt f hε
  refine ⟨g ⊔ 0, le_sup_right, ?_⟩
  rw [SupHomClass.map_sup, map_zero, ← sup_eq_left.mpr hf]
  exact (norm_sup_sub_sup_le_norm _ _ _).trans_lt
    (by simpa only [dist_eq_norm, norm_sub_rev] using hg)

private theorem fvl_minima_decreases (p : Exponent) (h : ℕ → Free p F)
    (hh : DecreasesToZero h) (g : ℕ → FVL F) (hgpos : ∀ n, 0 ≤ g n)
    (herr : Tendsto (fun n => ofFVL p (g n) - h n) atTop (𝓝 0)) :
    DecreasesToZero (fun n => ofFVL p ((Finset.range (n + 1)).inf'
      (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n)) g)) := by
  let f (n : ℕ) : FVL F := (Finset.range (n + 1)).inf'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n)) g
  have hfpos (n : ℕ) : 0 ≤ f n := Finset.le_inf' _ _ (fun i _ => hgpos i)
  have hfbound (n : ℕ) : ofFVL p (f n) ≤ ofFVL p (g n) :=
    (ofFVL p).monotone (Finset.inf'_le g (Finset.mem_range.mpr (Nat.lt_succ_self n)))
  change DecreasesToZero (fun n => ofFVL p (f n))
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro m n hmn
    apply (ofFVL p).monotone
    exact Finset.le_inf' _ _ (fun i hi => Finset.inf'_le g
      (Finset.range_mono (Nat.add_le_add_right hmn 1) hi))
  · rintro _ ⟨n, rfl⟩
    exact (ofFVL p).map_nonneg (hfpos n)
  · intro b hb
    apply hh.2.2
    rintro _ ⟨m, rfl⟩
    apply sub_nonpos.mp
    apply ge_of_tendsto herr
    exact (eventually_ge_atTop m).mono fun n hn =>
      sub_le_sub ((hb ⟨n, rfl⟩).trans (hfbound n)) (hh.1 hn)

private theorem sigma_test_of_fvl (p : Exponent) (S : LatticeOperator (Free p F) (Free p E))
    (htest : ∀ f : ℕ → FVL F, (∀ n, 0 ≤ f n) →
      DecreasesToZero (fun n => ofFVL p (f n)) →
      DecreasesToZero (fun n => S (ofFVL p (f n)))) : SigmaOrderContinuous S := by
  intro h hh
  refine ⟨S.toVecLatHom.monotone.comp_antitone hh.1, ⟨?_, ?_⟩⟩
  · rintro _ ⟨n, rfl⟩
    exact S.toVecLatHom.map_nonneg (hh.2.1 ⟨n, rfl⟩)
  · intro u hu
    by_contra hule
    let v := u ⊔ 0
    have hvpos : 0 ≤ v := le_sup_right
    have hvne : v ≠ 0 := fun hz => hule (hz ▸ le_sup_left)
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    have hvbound (n : ℕ) : v ≤ S (h n) := sup_le (hu ⟨n, rfl⟩)
      (S.toVecLatHom.map_nonneg (hh.2.1 ⟨n, rfl⟩))
    let C := ‖S.toContinuousLinearMap‖
    have hC : 0 ≤ C := norm_nonneg _
    let c (n : ℕ) : ℝ := ‖v‖ / (4 * (1 + C)) * (1 / 2 : ℝ) ^ n
    have hc (n : ℕ) : 0 < c n :=
      mul_pos (div_pos hvnorm (mul_pos (by norm_num) (by linarith))) (pow_pos (by norm_num) n)
    choose g hgpos hgerr using (fun n => positive_fvl_approximation p (h n)
      (hh.2.1 ⟨n, rfl⟩) (hc n))
    have hcsum : Summable c := summable_geometric_two.mul_left _
    have herr : Tendsto (fun n => ofFVL p (g n) - h n) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => (hgerr n).le) hcsum.tendsto_atTop_zero
    let f (n : ℕ) : FVL F := (Finset.range (n + 1)).inf'
      (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n)) g
    have hfpos (n : ℕ) : 0 ≤ f n := Finset.le_inf' _ _ (fun i _ => hgpos i)
    have hf := fvl_minima_decreases p h hh g hgpos herr
    let z (n : ℕ) : Free p E := |S (ofFVL p (g n) - h n)|
    have hzc (n : ℕ) : ‖z n‖ ≤ C * c n := by
      rw [norm_abs_eq_norm]
      exact (S.toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hgerr n).le hC)
    have hzsum : Summable z := (hcsum.mul_left C).of_norm_bounded hzc
    let e : Free p E := ∑' n, z n
    have hepos : 0 ≤ e := tsum_nonneg (fun n => abs_nonneg _)
    have hze (n : ℕ) : z n ≤ e := hzsum.le_tsum n (fun _ _ => abs_nonneg _)
    have hsum : HasSum (fun n => C * c n) (C * (‖v‖ / (2 * (1 + C)))) := by
      have heq : ‖v‖ / (4 * (1 + C)) * (∑' n : ℕ, (1 / 2 : ℝ) ^ n) =
          ‖v‖ / (2 * (1 + C)) := by
        rw [tsum_geometric_two]
        field_simp
        ring
      exact (heq ▸ summable_geometric_two.hasSum.mul_left (‖v‖ / (4 * (1 + C)))).mul_left C
    have henorm : ‖e‖ < ‖v‖ := (tsum_of_norm_bounded hsum hzc).trans_lt (by
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith)
    have hvg (n : ℕ) : v - e ≤ S (ofFVL p (g n)) := by
      have hz : S (h n) - S (ofFVL p (g n)) ≤ z n := by
        simpa only [z, map_sub, neg_sub] using neg_le_abs (S (ofFVL p (g n) - h n))
      exact (sub_le_sub (hvbound n) (hze n)).trans (sub_le_comm.mp hz)
    have hvf (n : ℕ) : v - e ≤ S (ofFVL p (f n)) := by
      change v - e ≤ S.toVecLatHom (ofFVL p ((Finset.range (n + 1)).inf' _ g))
      rw [map_finset_inf', map_finset_inf']
      exact Finset.le_inf' _ _ (fun i _ => hvg i)
    have hvle : v ≤ e := sub_nonpos.mp ((htest f hfpos hf).2.2
      (by rintro _ ⟨n, rfl⟩; exact hvf n))
    exact henorm.not_ge (norm_le_norm_of_abs_le_abs
      (by simpa only [abs_of_nonneg hvpos, abs_of_nonneg hepos] using hvle))

/-- Proposition 2.4 (`prop:fvl-sequential-test`): order continuity of an induced map
can be tested on positive sequences in the algebraic free lattice that decrease to zero
in `Free p F`. Norm density and lattice approximation reduce the general sequential test
to this common algebraic core. -/
theorem fvl_sequential_test (p : Exponent) (T : F →L[ℝ] E) :
    IsOrderContinuousOp (induced p T).toContinuousLinearMap.toLinearMap ↔
      ∀ f : ℕ → FVL F, (∀ n, 0 ≤ f n) →
        DecreasesToZero (fun n => ofFVL p (f n)) →
        DecreasesToZero (fun n => induced p T (ofFVL p (f n))) := by
  constructor
  · intro h f _ hf
    exact orderContinuous_sigmaOrderContinuous _
      (fun _ hx => (induced p T).toVecLatHom.map_nonneg hx) h _ hf
  · intro h
    exact (sigma_order_continuity p _
      (fun _ hx => (induced p T).toVecLatHom.map_nonneg hx)).mpr
        (sigma_test_of_fvl p (induced p T) h)

/-- Section 2: closed Banach-space ideals, via a linear Hahn--Banach extension isometry. -/
def IsBanachSpaceIdeal (M : Submodule ℝ E) : Prop :=
  IsClosed (M : Set E) ∧ ∃ Φ : Dual M →ₗᵢ[ℝ] Dual E,
    ∀ (ψ : Dual M) (x : M), Φ ψ x = ψ x

/-- Section 2: equivalence with the annihilator-kernel definition. -/
theorem banachSpaceIdeal_iff_projection (M : Submodule ℝ E) :
    IsBanachSpaceIdeal M ↔ IsClosed (M : Set E) ∧
      ∃ P : Dual E →L[ℝ] Dual E, P.comp P = P ∧ ‖P‖ ≤ 1 ∧
        ∀ φ : Dual E, P φ = 0 ↔ ∀ x : M, φ x = 0 := by
  let R : Dual E →L[ℝ] Dual M := (ContinuousLinearMap.compL ℝ M E ℝ).flip M.subtypeL
  have hR (φ : Dual E) (x : M) : R φ x = φ x := rfl
  have hRnorm (φ : Dual E) : ‖R φ‖ ≤ ‖φ‖ := (R φ).opNorm_le_bound (norm_nonneg φ)
    (fun x => φ.le_opNorm x)
  have hRsurj : Function.Surjective R := by
    intro ψ
    obtain ⟨φ, hφ, _⟩ := exists_extension_norm_eq M ψ
    exact ⟨φ, ContinuousLinearMap.ext hφ⟩
  constructor
  · rintro ⟨hclosed, Φ, hext⟩
    refine ⟨hclosed, Φ.toContinuousLinearMap.comp R, ?_, ?_, ?_⟩
    · apply ContinuousLinearMap.ext
      intro φ
      change Φ (R (Φ (R φ))) = Φ (R φ)
      exact congrArg Φ (ContinuousLinearMap.ext (hext (R φ)))
    · refine (Φ.toContinuousLinearMap.comp R).opNorm_le_bound zero_le_one (fun φ => ?_)
      change ‖Φ (R φ)‖ ≤ 1 * ‖φ‖
      simpa only [Φ.norm_map, one_mul] using hRnorm φ
    · intro φ
      change Φ (R φ) = 0 ↔ _
      rw [map_eq_zero_iff Φ Φ.injective]
      exact ⟨fun h x => DFunLike.congr_fun h x, fun h => ContinuousLinearMap.ext h⟩
  · rintro ⟨hclosed, P, hP, hPnorm, hker⟩
    obtain ⟨L, hL⟩ := R.toLinearMap.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hRsurj)
    let Φ : Dual M →ₗ[ℝ] Dual E := P.toLinearMap.comp L
    have hL' (ψ : Dual M) (x : M) : L ψ x = ψ x :=
      DFunLike.congr_fun (DFunLike.congr_fun hL ψ) x
    have hext (ψ : Dual M) (x : M) : Φ ψ x = ψ x := by
      have hz : P (L ψ - P (L ψ)) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.mpr (DFunLike.congr_fun hP (L ψ)).symm
      have hx := (hker _).mp hz x
      change L ψ x - P (L ψ) x = 0 at hx
      exact (sub_eq_zero.mp hx).symm.trans (hL' ψ x)
    have hnorm (ψ : Dual M) : ‖Φ ψ‖ = ‖ψ‖ := by
      apply le_antisymm
      · obtain ⟨φ, hφ, hnormφ⟩ := exists_extension_norm_eq M ψ
        have heq : Φ ψ = P φ := by
          apply sub_eq_zero.mp
          change P (L ψ) - P φ = 0
          rw [← map_sub]
          exact (hker _).mpr (fun x => by simp [hL' ψ x, hφ x])
        rw [heq]
        calc
          ‖P φ‖ ≤ ‖P‖ * ‖φ‖ := P.le_opNorm φ
          _ ≤ ‖φ‖ := mul_le_of_le_one_left (norm_nonneg _) hPnorm
          _ = ‖ψ‖ := hnormφ
      · apply ψ.opNorm_le_bound (norm_nonneg _)
        intro x
        rw [← hext ψ x]
        exact (Φ ψ).le_opNorm x
    exact ⟨hclosed, ⟨Φ, hnorm⟩, hext⟩

/-- Restriction to invariant subspaces, retaining the original underlying operator. -/
def restrictOperator (T : F →L[ℝ] E) (M : Submodule ℝ F) (N : Submodule ℝ E)
    (h : ∀ x : M, T x ∈ N) : M →L[ℝ] N where
  toFun x := ⟨T x, h x⟩
  map_add' x y := Subtype.ext (map_add T (x : F) (y : F))
  map_smul' r x := Subtype.ext (map_smul T r (x : F))
  cont := (T.continuous.comp continuous_subtype_val).subtype_mk h

/-- A countable set can be closed under a countable family of finitary operations. -/
private theorem countable_finitary_hull {X : Type*} {I : ℕ → Type*}
    [∀ n, Countable (I n)] (f : ∀ n, I n → (Fin n → X) → X)
    (A : Set X) (hA : A.Countable) :
    ∃ B : Set X, A ⊆ B ∧ B.Countable ∧
      ∀ n i (a : Fin n → X), (∀ j, a j ∈ B) → f n i a ∈ B := by
  let L : FirstOrder.Language := ⟨I, fun _ => Empty⟩
  let : L.Structure X := ⟨fun {n} => f n, fun {_} => isEmptyElim⟩
  let S := FirstOrder.Language.Substructure.closure L A
  have : Countable (Σ n, L.Functions n) := inferInstanceAs (Countable (Σ n, I n))
  have : Countable S := hA.substructure_closure L
  exact ⟨S, FirstOrder.Language.Substructure.subset_closure, Set.to_countable _,
    fun _ i a ha => S.fun_mem i a ha⟩

/-- Countable rational data for finite systems of approximate norm inequalities. -/
abbrev IdealTest (n : ℕ) :=
  Σ m : ℕ, Σ k : ℕ,
    (Fin k → Fin n → ℚ) × (Fin k → Fin m → ℚ) × (Fin k → ℚ) × Fin m

/-- Choose vectors satisfying a finite rational norm test, or zero if none exist. -/
def idealTestWitness {n m k : ℕ} (r : Fin k → Fin n → ℚ)
    (q : Fin k → Fin m → ℚ) (t : Fin k → ℚ) (a : Fin n → E) : Fin m → E := by
  classical
  exact if h : ∃ z : Fin m → E, ∀ i,
      ‖(∑ j, (r i j : ℝ) • a j) + ∑ j, (q i j : ℝ) • z j‖ < t i
    then h.choose else 0

/-- Closure under approximate witnesses for finite rational norm inequalities. -/
def HasNormWitnesses (B : Set E) : Prop :=
  ∀ (n m k : ℕ) (a : Fin n → E), (∀ j, a j ∈ B) →
    ∀ (x : Fin m → E) (r : Fin k → Fin n → ℚ) (q : Fin k → Fin m → ℚ)
      (ε : ℝ), 0 < ε → ∃ z : Fin m → E, (∀ j, z j ∈ B) ∧ ∀ i,
        ‖(∑ j, (r i j : ℝ) • a j) + ∑ j, (q i j : ℝ) • z j‖ <
          ‖(∑ j, (r i j : ℝ) • a j) + ∑ j, (q i j : ℝ) • x j‖ + ε

/-- Close under chosen witnesses for finite rational norm inequalities. -/
private theorem countable_norm_hull (A : Set E) (hA : A.Countable) :
    ∃ B : Set E, A ⊆ B ∧ (0 : E) ∈ B ∧ B.Countable ∧
      HasNormWitnesses B := by
  classical
  let f (n : ℕ) (d : IdealTest n) (a : Fin n → E) : E :=
    idealTestWitness d.2.2.1 d.2.2.2.1 d.2.2.2.2.1 a d.2.2.2.2.2
  obtain ⟨B, hAB, hB, hclosed⟩ := countable_finitary_hull f (insert 0 A) (hA.insert 0)
  refine ⟨B, fun _ h => hAB (mem_insert_of_mem _ h), hAB (mem_insert _ _), hB, ?_⟩
  intro n m k a ha x r q ε hε
  choose t htl htu using fun i : Fin k => exists_rat_btwn
    (show ‖(∑ j, (r i j : ℝ) • a j) + ∑ j, (q i j : ℝ) • x j‖ <
      ‖(∑ j, (r i j : ℝ) • a j) + ∑ j, (q i j : ℝ) • x j‖ + ε from lt_add_of_pos_right _ hε)
  have hex : ∃ z : Fin m → E, ∀ i,
      ‖(∑ j, (r i j : ℝ) • a j) + ∑ j, (q i j : ℝ) • z j‖ < t i := ⟨x, htl⟩
  refine ⟨idealTestWitness r q t a, fun j => hclosed n ⟨m, k, r, q, t, j⟩ a ha, ?_⟩
  intro i
  unfold idealTestWitness
  rw [dite_eq_left hex]
  exact (hex.choose_spec i).trans (htu i)

private theorem HasNormWitnesses.finite {B : Set E} (hB : HasNormWitnesses B)
    {α β γ : Type*} [Fintype α] [Fintype β] [Finite γ]
    (a : α → E) (ha : ∀ j, a j ∈ B) (x : β → E)
    (r : γ → α → ℚ) (q : γ → β → ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : β → E, (∀ j, z j ∈ B) ∧ ∀ i,
      ‖(∑ j, (r i j : ℝ) • a j) + ∑ j, (q i j : ℝ) • z j‖ <
        ‖(∑ j, (r i j : ℝ) • a j) + ∑ j, (q i j : ℝ) • x j‖ + ε := by
  classical
  let := Fintype.ofFinite γ
  let ea := (Fintype.equivFin α).symm
  let eb := (Fintype.equivFin β).symm
  let ec := (Fintype.equivFin γ).symm
  obtain ⟨z, hz, hnorm⟩ := hB _ _ _ (a ∘ ea) (fun j => ha _) (x ∘ eb)
    (fun i j => r (ec i) (ea j)) (fun i j => q (ec i) (eb j)) ε hε
  refine ⟨z ∘ eb.symm, fun j => hz _, fun i => ?_⟩
  have h := hnorm (ec.symm i)
  simp only [Equiv.apply_symm_apply, Function.comp_apply] at h ⊢
  have hr : ∑ j, (r i (ea j) : ℝ) • a (ea j) = ∑ j, (r i j : ℝ) • a j :=
    Equiv.sum_comp ea (fun j => (r i j : ℝ) • a j)
  have hx : ∑ j, (q i (eb j) : ℝ) • x (eb j) = ∑ j, (q i j : ℝ) • x j :=
    Equiv.sum_comp eb (fun j => (q i j : ℝ) • x j)
  have hz' : ∑ j, (q i (eb j) : ℝ) • z j = ∑ j, (q i j : ℝ) • z (eb.symm j) := by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.sum_comp eb (fun j => (q i j : ℝ) • z (eb.symm j)))
  simpa only [hr, hx, hz'] using h

/-- The canonical bidual evaluation of a subspace, viewed in its weak-star bidual. -/
def idealBidualEval (M : Submodule ℝ E) : M →ₗ[ℝ] WeakDual ℝ (Dual M) :=
  StrongDual.toWeakDual.toLinearMap.comp (NormedSpace.inclusionInDoubleDual ℝ M).toLinearMap

private theorem idealBidualEval_norm (M : Submodule ℝ E) (x : M) :
    ‖(idealBidualEval M x).toStrongDual‖ = ‖x‖ :=
  (NormedSpace.inclusionInDoubleDualLi ℝ).norm_map x

private theorem HasNormWitnesses.finite_model {B : Set E} (hB : HasNormWitnesses B)
    (M : Submodule ℝ E) (hBM : B ⊆ M)
    (s : Finset ((E →₀ ℚ) × B)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ R : E → WeakDual ℝ (Dual M),
      (∀ x, ‖(R x).toStrongDual‖ ≤ ‖x‖ + 1) ∧
      ∀ j ∈ s,
        ‖(j.1.sum (fun x q => (q : ℝ) • R x) - idealBidualEval M ⟨j.2, hBM j.2.2⟩).toStrongDual‖ <
          ‖j.1.sum (fun x q => (q : ℝ) • x) - j.2.1‖ + ε := by
  classical
  let t : Finset E := s.biUnion (fun j => j.1.support)
  have ht (j : s) : j.1.1.support ⊆ t := fun x hx => Finset.mem_biUnion.mpr ⟨j.1, j.2, hx⟩
  let a : s → E := fun j => j.1.2.1
  let r : s ⊕ t → s → ℚ := fun i j => match i with
    | .inl k => if j = k then -1 else 0
    | .inr _ => 0
  let q : s ⊕ t → t → ℚ := fun i j => match i with
    | .inl k => k.1.1 j
    | .inr k => if j = k then 1 else 0
  obtain ⟨z, hz, hnorm⟩ := hB.finite a (fun j => j.1.2.2) Subtype.val r q hε
  have hznorm (x : t) : ‖z x‖ < ‖(x : E)‖ + ε := by
    simpa [r, q, apply_ite, ite_smul] using hnorm (Sum.inr x)
  let zM (x : t) : M := ⟨z x, hBM (hz x)⟩
  let R (x : E) : WeakDual ℝ (Dual M) :=
    if hx : x ∈ t then idealBidualEval M (zM ⟨x, hx⟩) else 0
  have hR (x : t) : R x = idealBidualEval M (zM x) := by simp [R]
  refine ⟨R, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ t
    · rw [show R x = idealBidualEval M (zM ⟨x, hx⟩) from hR ⟨x, hx⟩,
        idealBidualEval_norm]
      exact (hznorm ⟨x, hx⟩).le.trans (add_le_add le_rfl hε1)
    · rw [show R x = 0 by simp [R, hx]]
      change ‖(0 : Dual (Dual M))‖ ≤ ‖x‖ + 1
      simp only [norm_zero]
      positivity
  · intro j hj
    have htest := hnorm (Sum.inl (⟨j, hj⟩ : s))
    simp only [r, q, apply_ite, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
      ite_smul, neg_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] at htest
    have hsum {V : Type u} [AddCommGroup V] [Module ℝ V] (f : E → V) :
        j.1.sum (fun x q => (q : ℝ) • f x) = ∑ x : t, (j.1 x : ℝ) • f x := by
      rw [Finsupp.sum_of_support_subset j.1 (ht ⟨j, hj⟩) _ (by simp)]
      exact (Finset.sum_attach t _).symm
    rw [hsum R, hsum (fun x : E => x)]
    have heq : (∑ x : t, (j.1 x : ℝ) • R x) - idealBidualEval M ⟨j.2, hBM j.2.2⟩ =
        idealBidualEval M ((∑ x : t, (j.1 x : ℝ) • zM x) - ⟨j.2, hBM j.2.2⟩) := by
      simp only [map_sub, map_sum, map_smul, hR]
    rw [heq, idealBidualEval_norm]
    change ‖((∑ x : t, (j.1 x : ℝ) • zM x) - ⟨j.2, hBM j.2.2⟩ : M).val‖ < _
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul]
    change ‖(∑ x : t, (j.1 x : ℝ) • z x) - j.2.1‖ < _
    simpa only [a, sub_eq_add_neg, add_comm] using htest

/-- Weak-star compactness realizes all finite rational norm constraints simultaneously. -/
private theorem HasNormWitnesses.bidual_model {B : Set E} (hB : HasNormWitnesses B)
    (M : Submodule ℝ E) (hBM : B ⊆ M) :
    ∃ R : E → WeakDual ℝ (Dual M), ∀ (c : E →₀ ℚ) (b : B),
      ‖(c.sum (fun x q => (q : ℝ) • R x) - idealBidualEval M ⟨b, hBM b.2⟩).toStrongDual‖ ≤
        ‖c.sum (fun x q => (q : ℝ) • x) - b.1‖ := by
  classical
  let Ω : Set (E → WeakDual ℝ (Dual M)) := {R | ∀ x, ‖(R x).toStrongDual‖ ≤ ‖x‖ + 1}
  have hΩ : IsCompact Ω := by
    apply isCompact_pi_infinite (s := fun x : E =>
      {φ : WeakDual ℝ (Dual M) | ‖φ.toStrongDual‖ ≤ ‖x‖ + 1})
    intro x
    convert WeakDual.isCompact_closedBall (0 : Dual (Dual M)) (‖x‖ + 1) using 1
    ext φ
    simp only [mem_ofPred_eq, mem_preimage, Metric.mem_closedBall, dist_zero_right]
  let I := ((E →₀ ℚ) × B) × {ε : ℝ // 0 < ε}
  let C (i : I) : Set (E → WeakDual ℝ (Dual M)) := {R |
    ‖(i.1.1.sum (fun x q => (q : ℝ) • R x) - idealBidualEval M ⟨i.1.2, hBM i.1.2.2⟩).toStrongDual‖ ≤
      ‖i.1.1.sum (fun x q => (q : ℝ) • x) - i.1.2.1‖ + i.2.1}
  have hC (i : I) : IsClosed (C i) := by
    have hc : Continuous (fun R : E → WeakDual ℝ (Dual M) =>
        i.1.1.sum (fun x q => (q : ℝ) • R x) - idealBidualEval M ⟨i.1.2, hBM i.1.2.2⟩) := by
      exact (continuous_finsetSum i.1.1.support
        (fun x _ => (show Continuous (fun R : E → WeakDual ℝ (Dual M) => R x)
          from continuous_apply x).const_smul (i.1.1 x : ℝ))).sub continuous_const
    convert (WeakDual.isClosed_closedBall (0 : Dual (Dual M))
      (‖i.1.1.sum (fun x q => (q : ℝ) • x) - i.1.2.1‖ + i.2.1)).preimage hc using 1
    ext R
    simp only [C, mem_ofPred_eq, mem_preimage, Metric.mem_closedBall, dist_zero_right]
  obtain ⟨R, _, hR⟩ := hΩ.inter_iInter_nonempty C hC (by
    intro s
    obtain ⟨δ, hδ, hδle⟩ := finite_positive_lower_bound s (fun i => i.2.1) (fun i _ => i.2.2)
    obtain ⟨R, hRn, hRc⟩ := hB.finite_model M hBM (s.image Prod.fst)
      (lt_min hδ zero_lt_one) (min_le_right δ 1)
    refine ⟨R, hRn, ?_⟩
    simp only [mem_iInter]
    intro i hi
    exact (hRc i.1 (Finset.mem_image_of_mem _ hi)).le.trans
      (add_le_add le_rfl ((min_le_left δ 1).trans (hδle i hi))))
  refine ⟨R, fun c b => ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  exact mem_iInter.mp hR ⟨⟨c, b⟩, ⟨ε, hε⟩⟩

private theorem HasNormWitnesses.linear_bidual_model {B : Set E}
    (hB : HasNormWitnesses B) (h0 : (0 : E) ∈ B)
    (M : Submodule ℝ E) (hBM : B ⊆ M) :
    ∃ R : E →L[ℝ] Dual (Dual M), (∀ x, ‖R x‖ ≤ ‖x‖) ∧
      ∀ b : B, R b = NormedSpace.inclusionInDoubleDual ℝ M ⟨b, hBM b.2⟩ := by
  classical
  obtain ⟨R, hR⟩ := hB.bidual_model M hBM
  have hsum_add {V : Type u} [AddCommGroup V] [Module ℝ V]
      (f : E → V) (c d : E →₀ ℚ) :
      (c + d).sum (fun x q => (q : ℝ) • f x) =
        c.sum (fun x q => (q : ℝ) • f x) + d.sum (fun x q => (q : ℝ) • f x) := by
    exact Finsupp.sum_add_index (by simp) (by intros; simp only [Rat.cast_add, add_smul])
  have hsingle {V : Type u} [AddCommGroup V] [Module ℝ V]
      (f : E → V) (x : E) (q : ℚ) :
      (Finsupp.single x q).sum (fun x q => (q : ℝ) • f x) = (q : ℝ) • f x :=
    Finsupp.sum_single_index (by simp)
  have hnorm (x : E) : ‖(R x).toStrongDual‖ ≤ ‖x‖ := by
    have h := hR (Finsupp.single x 1) ⟨0, h0⟩
    rw [hsingle R] at h
    simpa only [hsingle, Rat.cast_one, one_smul,
      show (⟨(0 : E), hBM h0⟩ : M) = 0 from rfl, map_zero, sub_zero] using h
  have hz : (R 0).toStrongDual = 0 := by
    have hh : ‖(R 0).toStrongDual‖ ≤ 0 := by simpa only [norm_zero] using hnorm 0
    exact (norm_le_zero_iff (a := (R 0).toStrongDual)).mp hh
  have hadd (x y : E) : (R (x + y)).toStrongDual = (R x).toStrongDual + (R y).toStrongDual := by
    have h := hR (Finsupp.single (x + y) 1 + Finsupp.single x (-1) + Finsupp.single y (-1)) ⟨0, h0⟩
    simp only [hsum_add R, hsingle R, hsum_add (fun x : E => x),
      hsingle (fun x : E => x), Rat.cast_one,
      Rat.cast_neg, one_smul, neg_smul, show (⟨(0 : E), hBM h0⟩ : M) = 0 from rfl,
      map_zero, sub_zero] at h
    have hrhs : x + y + -x + -y = 0 := by abel
    rw [hrhs, norm_zero] at h
    have h := (norm_le_zero_iff (a := (R (x + y) + -R x + -R y).toStrongDual)).mp h
    change (R (x + y)).toStrongDual + -(R x).toStrongDual + -(R y).toStrongDual = 0 at h
    exact eq_of_sub_eq_zero (by convert h using 1; abel)
  let L : E →+ Dual (Dual M) := ⟨⟨fun x => (R x).toStrongDual, hz⟩, hadd⟩
  have hcont : Continuous L :=
    (AddMonoidHomClass.lipschitz_of_bound L 1 (fun x => by
      change ‖(R x).toStrongDual‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using hnorm x)).continuous
  refine ⟨L.toRealLinearMap hcont, hnorm, fun b => ?_⟩
  have h := hR (Finsupp.single b.1 1) b
  simp only [hsingle R, hsingle (fun x : E => x), Rat.cast_one, one_smul,
    sub_self, norm_zero] at h
  exact sub_eq_zero.mp ((norm_le_zero_iff (a :=
    (R b.1 - idealBidualEval M ⟨b, hBM b.2⟩).toStrongDual)).mp h)

/-- Transposing the bidual contraction gives linear isometric Hahn–Banach extensions. -/
private theorem HasNormWitnesses.isIdeal {B : Set E} (hB : HasNormWitnesses B)
    (h0 : (0 : E) ∈ B) :
    IsBanachSpaceIdeal (Submodule.span ℝ B).topologicalClosure := by
  let M := (Submodule.span ℝ B).topologicalClosure
  have hBM : B ⊆ M := fun x hx => Submodule.le_topologicalClosure _ (Submodule.subset_span hx)
  obtain ⟨R, hRn, hRb⟩ := hB.linear_bidual_model h0 M hBM
  let Φ : Dual M →ₗ[ℝ] Dual E :=
    { toFun := fun ψ => (ContinuousLinearMap.apply ℝ ℝ ψ).comp R
      map_add' := fun ψ χ => by ext x; exact (R x).map_add ψ χ
      map_smul' := fun c ψ => by ext x; exact (R x).map_smul c ψ }
  have hΦ (ψ : Dual M) (x : E) : Φ ψ x = R x ψ := rfl
  have hext (ψ : Dual M) (x : M) : Φ ψ x = ψ x := by
    obtain ⟨φ, hφ, _⟩ := exists_extension_norm_eq M ψ
    have hker : M ≤ (Φ ψ - φ).ker := by
      apply Submodule.topologicalClosure_minimal
      · apply Submodule.span_le.mpr
        intro b hb
        change Φ ψ b - φ b = 0
        rw [hΦ, hRb ⟨b, hb⟩]
        exact sub_eq_zero.mpr (hφ ⟨b, hBM hb⟩).symm
      · exact (Φ ψ - φ).isClosed_ker
    have hx := hker x.2
    change Φ ψ x - φ x = 0 at hx
    exact (sub_eq_zero.mp hx).trans (hφ x)
  have hnorm (ψ : Dual M) : ‖Φ ψ‖ = ‖ψ‖ := by
    apply le_antisymm
    · apply (Φ ψ).opNorm_le_bound (norm_nonneg ψ)
      intro x
      rw [hΦ]
      exact ((R x).le_opNorm ψ).trans (by nlinarith [hRn x, norm_nonneg ψ])
    · apply ψ.opNorm_le_bound (norm_nonneg _)
      intro x
      rw [← hext ψ x]
      exact (Φ ψ).le_opNorm x
  exact ⟨(Submodule.span ℝ B).isClosed_topologicalClosure, ⟨Φ, hnorm⟩, hext⟩

/-- The cited separable-ideal existence result used in Lemma 2.5. -/
theorem separable_ideal_exists (A : Set E) (hA : A.Countable) :
    ∃ M : Submodule ℝ E, A ⊆ M ∧ IsBanachSpaceIdeal M ∧
      TopologicalSpace.SeparableSpace M := by
  obtain ⟨B, hAB, h0, hBc, hB⟩ := countable_norm_hull A hA
  refine ⟨(Submodule.span ℝ B).topologicalClosure, ?_, hB.isIdeal h0, ?_⟩
  · exact hAB.trans (fun x hx => Submodule.le_topologicalClosure _ (Submodule.subset_span hx))
  · exact hBc.isSeparable.span.closure.separableSpace

/-- Isometric linear extension of dual functionals preserves admissible families. -/
theorem normAdmissible_linearIsometry (p : Exponent)
    (Φ : Dual F →ₗᵢ[ℝ] Dual E) {n : ℕ} (ψ : Fin n → Dual F)
    (hψ : NormAdmissible p ψ) : NormAdmissible p (fun i => Φ (ψ i)) := by
  intro x hx
  let y : PiLp p.1 (fun _ : Fin n => ℝ) := WithLp.toLp p.1 (fun i => Φ (ψ i) x)
  obtain ⟨l, hl, hly⟩ := exists_dual_vector'' ℝ y
  change l y = ‖y‖ at hly
  let a : Fin n → ℝ := fun i => l (PiLp.single p.1 i 1)
  have hlin (z : Fin n → ℝ) : ∑ i, a i * z i = l (WithLp.toLp p.1 z) := by
    have hz := (PiLp.basisFun p.1 ℝ (Fin n)).sum_repr (WithLp.toLp p.1 z)
    simpa [a, map_sum, map_smul, smul_eq_mul, mul_comm] using congrArg l hz
  let θ : Dual F := ∑ i, a i • ψ i
  have hθ : ‖θ‖ ≤ 1 := by
    apply θ.opNorm_le_bound zero_le_one
    intro z
    change ‖(∑ i, a i • ψ i) z‖ ≤ 1 * ‖z‖
    simp only [sum_apply, smul_apply, smul_eq_mul,
      hlin, one_mul]
    exact (l.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hl (norm_nonneg _)).trans
      (by simpa only [one_mul, ← scalarPSum_eq_piLp_norm] using
        normAdmissible_eval_le_norm p ψ hψ z))
  have hbound := (Φ θ).le_opNorm x
  have heq : Φ θ x = l y := by
    simp only [θ, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, hlin]
    rfl
  rw [heq, hly, Φ.norm_map, Real.norm_of_nonneg (norm_nonneg _)] at hbound
  exact (show scalarPSum p (fun i => Φ (ψ i) x) ≤ ‖θ‖ * ‖x‖ from
    (scalarPSum_eq_piLp_norm p _).trans_le hbound).trans
      (by nlinarith [norm_nonneg θ, norm_nonneg x])

/-- Section 2: ideal inclusions induce isometric embeddings. -/
theorem ideal_induced_isometry (p : Exponent)
    (M : Submodule ℝ E) (hM : IsBanachSpaceIdeal M) :
    Isometry (induced p M.subtypeL) := by
  obtain ⟨_, Φ, hext⟩ := hM
  have hrestrict (ψ : Dual M) : (Φ ψ).comp M.subtypeL = ψ :=
    ContinuousLinearMap.ext (hext ψ)
  apply AddMonoidHomClass.isometry_of_norm (induced p M.subtypeL).toContinuousLinearMap
  intro f
  apply le_antisymm
  · have hnorm : ‖M.subtypeL‖ ≤ 1 := M.subtypeL.opNorm_le_bound zero_le_one
      (fun x => by simp)
    exact ((induced p M.subtypeL).toContinuousLinearMap.le_opNorm f).trans (by
      rw [(induced_norm_generators p M.subtypeL).1]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hnorm (norm_nonneg f))
  · apply (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).mp
    rw [← freeNormExt_eq_norm p f, ← freeNormExt_eq_norm p (induced p M.subtypeL f)]
    by_cases htop : p.1 = ⊤
    · simp only [freeNormExt, ite_eq_left htop]
      refine iSup_le fun ψ => iSup_le fun hψ => ?_
      exact le_iSup_of_le (Φ ψ) (le_iSup_of_le (by simpa only [Φ.norm_map] using hψ)
        (by rw [canonical_map_formulas, hrestrict]))
    · simp only [freeNormExt, ite_eq_right htop]
      refine iSup_le fun n => iSup_le fun ψ => iSup_le fun hψ => ?_
      exact le_iSup_of_le n (le_iSup_of_le (fun i => Φ (ψ i))
        (le_iSup_of_le (normAdmissible_linearIsometry p Φ ψ hψ)
          (by simp only [canonical_map_formulas, hrestrict]; exact le_rfl)))

/-- Each lattice expression depends on finitely many generators. -/
theorem fvl_finite_generators (p : Exponent) (f : FVL E) :
    ∃ A : Set E, A.Finite ∧ ∀ M : Submodule ℝ E, A ⊆ M →
      ofFVL p f ∈ Set.range (induced p M.subtypeL) := by
  obtain ⟨n, x, e, he⟩ := FVLv.exists_eval_of_eq f
  refine ⟨Set.range x, Set.finite_range _, fun M hM => ?_⟩
  refine ⟨LLexpr.eval (fun i => delta p (⟨x i, hM (Set.mem_range_self i)⟩ : M)) e, ?_⟩
  change (induced p M.subtypeL).toVecLatHom _ = _
  rw [LLexpr.map_eval]
  rw [← he, LLexpr.map_eval]
  congr 1
  funext i
  exact ((induced_norm_generators p M.subtypeL).2 _).trans (ofFVL_of p (x i)).symm

/-- Countably many generators suffice to lift a free element through an ideal inclusion. -/
private theorem free_countable_generators (p : Exponent) (f : Free p E) :
    ∃ A : Set E, A.Countable ∧ ∀ M : Submodule ℝ E, IsBanachSpaceIdeal M → A ⊆ M →
      f ∈ Set.range (induced p M.subtypeL) := by
  obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.mp (denseRange_ofFVL p f)
  choose v hv using hw
  have hvlim : Tendsto (fun n => ofFVL p (v n)) atTop (𝓝 f) := by
    simpa only [hv] using hlim
  choose A hA hgen using fun n => fvl_finite_generators p (v n)
  refine ⟨⋃ n, A n, Set.countable_iUnion (fun n => (hA n).countable), fun M hM hAM => ?_⟩
  apply (ideal_induced_isometry p M hM).isClosedEmbedding.isClosed_range.mem_of_tendsto hvlim
  exact Eventually.of_forall (fun n => hgen n M (fun x hx => hAM (Set.mem_iUnion.mpr ⟨n, hx⟩)))

private theorem banachSpaceIdeal_top : IsBanachSpaceIdeal (⊤ : Submodule ℝ E) := by
  apply (banachSpaceIdeal_iff_projection _).mpr
  refine ⟨isClosed_univ, ContinuousLinearMap.id ℝ (Dual E), rfl,
    ContinuousLinearMap.norm_id_le, fun φ => ?_⟩
  constructor
  · intro h x
    exact congrArg (fun ψ : Dual E => ψ x) h
  · intro h
    exact ContinuousLinearMap.ext (fun x => h ⟨x, Submodule.mem_top⟩)

private theorem separable_ideal_containing (A : Set E) (hA : A.Countable) :
    ∃ M : Submodule ℝ E, A ⊆ M ∧ IsBanachSpaceIdeal M ∧
      TopologicalSpace.SeparableSpace M ∧ (TopologicalSpace.SeparableSpace E → M = ⊤) := by
  classical
  by_cases hE : TopologicalSpace.SeparableSpace E
  · let := hE
    exact ⟨⊤, fun _ _ => Submodule.mem_top, banachSpaceIdeal_top, inferInstance, fun _ => rfl⟩
  · obtain ⟨M, hAM, hM, hMs⟩ := separable_ideal_exists A hA
    exact ⟨M, hAM, hM, hMs, fun h => (hE h).elim⟩

/-- Lemma 2.5 (`lem:separable-reduction`): failure of order continuity is witnessed
on separable Banach-space ideals M and N with T(M) contained in N. The restriction of T
still induces a map that fails order continuity. If the original domain is separable,
M can be taken to be the whole domain. -/
theorem separable_reduction [CompleteSpace E] [CompleteSpace F]
    (p : Exponent) (T : F →L[ℝ] E)
    (hT : ¬ IsOrderContinuousOp (induced p T).toContinuousLinearMap.toLinearMap) :
    ∃ (M : Submodule ℝ F) (N : Submodule ℝ E) (h : ∀ x : M, T x ∈ N),
      IsBanachSpaceIdeal M ∧ IsBanachSpaceIdeal N ∧
      TopologicalSpace.SeparableSpace M ∧ TopologicalSpace.SeparableSpace N ∧
      (TopologicalSpace.SeparableSpace F → M = ⊤) ∧
      ¬ IsOrderContinuousOp
        (induced p (restrictOperator T M N h)).toContinuousLinearMap.toLinearMap := by
  classical
  let S := induced p T
  obtain ⟨f, hf, g, hg, hg0⟩ : ∃ f : ℕ → Free p F, DecreasesToZero f ∧
      ∃ g : Free p E, (∀ n, g ≤ S (f n)) ∧ ¬ g ≤ 0 := by
    by_contra! h
    apply hT
    apply (sigma_order_continuity p _ (fun _ hx => S.toVecLatHom.map_nonneg hx)).mpr
    intro f hf
    refine ⟨S.toVecLatHom.monotone.comp_antitone hf.1, ⟨?_, ?_⟩⟩
    · rintro _ ⟨n, rfl⟩
      exact S.toVecLatHom.map_nonneg (hf.2.1 ⟨n, rfl⟩)
    · intro g hg
      exact h f hf g (fun n => hg ⟨n, rfl⟩)
  choose A hAc hAf using fun n => free_countable_generators p (f n)
  obtain ⟨M, hAM, hM, hMs, hMtop⟩ := separable_ideal_containing (⋃ n, A n)
    (Set.countable_iUnion hAc)
  let := hMs
  let : CompleteSpace M := hM.1.isComplete.completeSpace_coe
  have hfM (n : ℕ) : f n ∈ Set.range (induced p M.subtypeL) :=
    hAf n M hM (fun x hx => hAM (Set.mem_iUnion.mpr ⟨n, hx⟩))
  choose fM hfM using hfM
  obtain ⟨B, hBc, hBg⟩ := free_countable_generators p g
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense M
  obtain ⟨N, hBN, hN, hNs⟩ := separable_ideal_exists
    (B ∪ (fun x : M => T x) '' D) (hBc.union (hDc.image _))
  let := hNs
  let : CompleteSpace N := hN.1.isComplete.completeSpace_coe
  have hTN (x : M) : T x ∈ N := by
    have hc : IsClosed {x : M | T x ∈ N} :=
      hN.1.preimage (T.continuous.comp continuous_subtype_val)
    exact hc.closure_subset_iff.mpr (fun y hy => hBN (Or.inr ⟨y, hy, rfl⟩)) (hDd x)
  obtain ⟨gN, hgN⟩ := hBg N hN (fun x hx => hBN (Or.inl hx))
  refine ⟨M, N, hTN, hM, hN, hMs, hNs, hMtop, ?_⟩
  let J := induced p M.subtypeL
  let K := induced p N.subtypeL
  let U := induced p (restrictOperator T M N hTN)
  have hJ : Function.Injective J := (ideal_induced_isometry p M hM).injective
  have hK : Function.Injective K := (ideal_induced_isometry p N hN).injective
  have hdec : DecreasesToZero fM := by
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · intro n m hnm
      apply J.toVecLatHom.le_of_map_le hJ
      change J (fM m) ≤ J (fM n)
      rw [hfM, hfM]
      exact hf.1 hnm
    · rintro _ ⟨n, rfl⟩
      apply J.toVecLatHom.le_of_map_le hJ
      change J 0 ≤ J (fM n)
      rw [map_zero J.toContinuousLinearMap, hfM]
      exact hf.2.1 ⟨n, rfl⟩
    · intro z hz
      apply J.toVecLatHom.le_of_map_le hJ
      change J z ≤ J 0
      rw [map_zero J.toContinuousLinearMap]
      apply hf.2.2
      rintro _ ⟨n, rfl⟩
      rw [← hfM n]
      exact J.toVecLatHom.monotone (hz ⟨n, rfl⟩)
  have hcomm (a : Free p M) : K (U a) = S (J a) := by
    apply Subtype.ext
    apply Subtype.ext
    funext φ
    rfl
  have hlower (n : ℕ) : gN ≤ U (fM n) := by
    apply K.toVecLatHom.le_of_map_le hK
    change K gN ≤ K (U (fM n))
    rw [hcomm, hfM n, hgN]
    exact hg n
  intro hU
  have hc := orderContinuous_sigmaOrderContinuous U.toContinuousLinearMap.toLinearMap
    (fun _ hx => U.toVecLatHom.map_nonneg hx) hU fM hdec
  have hgle : gN ≤ 0 := hc.2.2 (by rintro _ ⟨n, rfl⟩; exact hlower n)
  apply hg0
  have hh := K.toVecLatHom.monotone hgle
  change K gN ≤ K 0 at hh
  simpa only [show K gN = g from hgN, map_zero] using hh

/-- Section 1: an isomorphic embedding is quantitatively bounded below. -/
def BoundedBelow {X : Type u} {Y : Type v} [Norm X] [Norm Y] (T : X → Y) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖T x‖

/-- Section 1's equivalent closed-range description. -/
theorem embedding_iff [CompleteSpace E] [CompleteSpace F] (T : F →L[ℝ] E) :
    BoundedBelow T ↔ Function.Injective T ∧ IsClosed (Set.range T) := by
  change (∃ c > 0, ∀ x, c * ‖x‖ ≤ ‖T x‖) ↔ _
  rw [← antilipschitzWith_iff_exists_mul_le_norm]
  exact ⟨fun ⟨_, h⟩ => ⟨h.injective, h.isClosed_range T.uniformContinuous⟩,
    fun ⟨hi, hc⟩ => T.antilipschitz_of_injective_of_isClosed_range hi hc⟩

/-- An isomorphic lattice embedding retains the order-reflecting and norm conditions. -/
def IsLatticeEmbedding {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [NormedVectorLattice X]
    [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [NormedVectorLattice Y]
    (T : LatticeOperator X Y) : Prop :=
  BoundedBelow T ∧ Function.Injective T ∧ ∀ x y, T x ≤ T y ↔ x ≤ y

/-- The positive algebraic sequence `(|δx + δy| - (n + 1)|δx - δy|) ⊔ 0`. For
distinct x and y it decreases to zero; if T identifies x and y, its induced image is
the constant `2 • |delta p (T x)|`. Used in Theorem 2.7 and Proposition 3.1. -/
def collisionSequence (x y : E) (n : ℕ) : FVL E :=
  (|FVLv.of x + FVLv.of y| - (n + 1 : ℝ) • |FVLv.of x - FVLv.of y|) ⊔ 0

private theorem collision_scalar_nonpos {a b c : ℝ} (hb : b ≠ 0)
    (h : ∀ n : ℕ, c ≤ max (|a| - (n + 1 : ℝ) * |b|) 0) : c ≤ 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (|a| / |b|)
  have hmul : |a| < (n : ℝ) * |b| := (div_lt_iff₀ (abs_pos.mpr hb)).mp hn
  have hle : |a| - (n + 1 : ℝ) * |b| ≤ 0 := by nlinarith [abs_nonneg b]
  simpa only [max_eq_right hle] using h n

private theorem nonpos_of_nonpos_off_kernel {D : Type*} [AddCommGroup D] [Module ℝ D]
    (b : D →ₗ[ℝ] ℝ) (hb : b ≠ 0) (g : D → ℝ)
    (hc : ∀ φ ψ, Continuous (fun t : ℝ => g (φ + t • ψ)))
    (hg : ∀ φ, b φ ≠ 0 → g φ ≤ 0) : ∀ φ, g φ ≤ 0 := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ, b ψ ≠ 0 := by
    by_contra! h
    exact hb (LinearMap.ext h)
  intro φ
  by_cases hφ : b φ = 0
  · have ht : Tendsto (fun t : ℝ => g (φ + t • ψ)) (𝓝[≠] 0) (𝓝 (g φ)) := by
      simpa using ((hc φ ψ).continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hg _ (by simpa [map_add, map_smul, hφ] using mul_ne_zero (by simpa using ht) hψ)
  · exact hg φ hφ

private theorem collisionSequence_apply (p : Exponent) (x y : E) (n : ℕ) (φ : Dual E) :
    ofFVL p (collisionSequence x y n) φ =
      max (|φ x + φ y| - (n + 1 : ℝ) * |φ x - φ y|) 0 := by
  have h : ofFVL p (collisionSequence x y n) =
      (|delta p x + delta p y| - (n + 1 : ℝ) • |delta p x - delta p y|) ⊔ 0 := by
    simp only [collisionSequence, SupHomClass.map_sup, map_sub, map_smul, VecLatHom.map_abs,
      map_add, ofFVL_of, map_zero]
  exact congrArg (fun f : Free p E => f φ) h

/-- For distinct vectors with the same image under T, the collision sequence decreases
to zero in the source while every image equals `2 • |delta p (T x)|`. The retained
nonzero-image hypothesis makes this a failure witness in Proposition 3.1; the displayed
identity and decrease themselves hold without using that hypothesis. -/
theorem collision_sequence_properties (p : Exponent) (T : F →L[ℝ] E) (x y : F) (hne : x ≠ y)
    (heq : T x = T y) (_hzero : T x ≠ 0) :
    DecreasesToZero (fun n => ofFVL p (collisionSequence x y n)) ∧
      ∀ n, induced p T (ofFVL p (collisionSequence x y n)) = 2 • |delta p (T x)| := by
  constructor
  · refine ⟨?_, ⟨?_, ?_⟩⟩
    · intro m n hmn
      apply (free_le_iff p _ _).2
      intro φ
      simp only [collisionSequence_apply]
      exact max_le_max_right 0 (by gcongr)
    · rintro _ ⟨n, rfl⟩
      apply (free_le_iff p _ _).2
      intro φ
      change 0 ≤ ofFVL p (collisionSequence x y n) φ
      rw [collisionSequence_apply]
      exact le_max_right _ _
    · intro g hg
      let b : Dual F →ₗ[ℝ] ℝ :=
        { toFun := fun φ => φ (x - y)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hb : b ≠ 0 := by
        intro hb
        obtain ⟨φ, _, hφ⟩ := exists_dual_vector'' ℝ (x - y)
        exact (sub_ne_zero.mpr hne) (norm_eq_zero.mp (hφ.symm.trans (DFunLike.congr_fun hb φ)))
      apply (free_le_iff p _ _).2
      intro φ
      change g φ ≤ 0
      apply nonpos_of_nonpos_off_kernel b hb g
        (fun ψ θ => (free_function_norm_continuous p g).comp
          (continuous_const.add (continuous_id.smul continuous_const))) _ φ
      intro ψ hψ
      apply collision_scalar_nonpos (a := ψ x + ψ y) (b := ψ x - ψ y)
        (by simpa only [b, LinearMap.coe_mk, AddHom.coe_mk, map_sub] using hψ)
      intro n
      simpa only [collisionSequence_apply] using (free_le_iff p _ _).1 (hg ⟨n, rfl⟩) ψ
  · intro n
    rw [two_smul]
    apply Subtype.ext
    apply Subtype.ext
    funext φ
    rw [canonical_map_formulas, collisionSequence_apply]
    change max (|φ (T x) + φ (T y)| - (n + 1 : ℝ) * |φ (T x) - φ (T y)|) 0 =
      |φ (T x)| + |φ (T x)|
    simp [heq, ← two_mul, abs_mul]

/-- Proposition 3.1 (`prop:injectivity`): if T is nonzero and its induced free-lattice
map is order continuous, then T is injective. Otherwise a collision sequence has a
constant nonzero image, contradicting preservation of decrease to zero. -/
theorem injectivity (p : Exponent)
    (T : F →L[ℝ] E) (hT : T ≠ 0)
    (h : IsOrderContinuousOp (induced p T).toContinuousLinearMap.toLinearMap) :
    Function.Injective T := by
  by_contra hn
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, T a = T b ∧ a ≠ b := by
    simpa only [Function.Injective, not_forall, exists_prop] using hn
  obtain ⟨v, hv⟩ : ∃ v, T v ≠ 0 := by
    by_contra! hz
    exact hT (ContinuousLinearMap.ext hz)
  have hxy : v + (a - b) ≠ v := by simpa using sub_ne_zero.mpr hne
  have hTv : T (v + (a - b)) = T v := by simp [map_add, map_sub, hab]
  obtain ⟨hf, himage⟩ := collision_sequence_properties p T (v + (a - b)) v hxy hTv
    (hTv ▸ hv)
  have hc := orderContinuous_sigmaOrderContinuous _
    (fun _ h => (induced p T).toVecLatHom.map_nonneg h) h _ hf
  have hle : 2 • |delta p (T (v + (a - b)))| ≤ 0 := hc.2.2 (by
    rintro _ ⟨n, rfl⟩
    exact le_of_eq (himage n).symm)
  obtain ⟨φ, _, hφ⟩ := exists_dual_vector'' ℝ (T v)
  have hreal := (free_le_iff p _ _).1 hle φ
  rw [two_smul] at hreal
  change |φ (T (v + (a - b)))| + |φ (T (v + (a - b)))| ≤ 0 at hreal
  rw [hTv, hφ] at hreal
  change |‖T v‖| + |‖T v‖| ≤ 0 at hreal
  rw [abs_norm] at hreal
  exact (norm_pos_iff.mpr hv).not_ge (by linarith)

/-- The finite nonempty minima in Proposition 3.2; index n means the first n+1 terms. -/
def evaluationMinima (p : Exponent) (u : ℕ → E) (n : ℕ) : Free p E :=
  Finset.univ.inf' Finset.univ_nonempty (fun i : Fin (n + 1) => |delta p (u i)|)

/-- Proposition 3.2's finite-dimensional escape lemma. -/
theorem finite_dimensional_escape [CompleteSpace E] (u : ℕ → E)
    (hb : Bornology.IsBounded (Set.range u))
    (hn : ¬ ∃ (a : ℕ → ℕ) (x : E), StrictMono a ∧ Tendsto (u ∘ a) atTop (𝓝 x)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ M : Submodule ℝ E, FiniteDimensional ℝ M →
      ∃ n, ε < Metric.infDist (u n) (M : Set E) := by
  by_contra h
  push Not at h
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  have htb : TotallyBounded (Set.range u) := by
    apply Metric.totallyBounded_iff.mpr
    intro ε hε
    obtain ⟨M, hM, hdist⟩ := h (ε / 4) (by positivity)
    let := hM
    let K : Set E := Subtype.val '' Metric.closedBall (0 : M) (C + ε / 2)
    have hK : IsCompact K := (isCompact_closedBall (0 : M) (C + ε / 2)).image
      continuous_subtype_val
    obtain ⟨s, hs, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded
      (ε / 2) (by positivity)
    refine ⟨s, hs, ?_⟩
    rintro _ ⟨n, rfl⟩
    obtain ⟨z, hz, hzu⟩ := (Metric.infDist_lt_iff (r := ε / 2) (show (M : Set E).Nonempty from
      ⟨0, M.zero_mem⟩)).mp (lt_of_le_of_lt (hdist n) (by linarith))
    have hzK : z ∈ K := by
      refine ⟨⟨z, hz⟩, ?_, rfl⟩
      change dist z 0 ≤ C + ε / 2
      have hnorm := dist_triangle z (u n) 0
      have hu := hC _ (Set.mem_range_self n)
      rw [dist_zero_right, dist_zero_right, dist_comm z (u n)] at hnorm
      rw [dist_zero_right]
      linarith
    obtain ⟨y, hy, hyz⟩ := Set.mem_iUnion₂.mp (hcover hzK)
    apply Set.mem_iUnion₂.mpr
    refine ⟨y, hy, ?_⟩
    exact (dist_triangle (u n) z y).trans_lt (by
      have hzy := Metric.mem_ball.mp hyz
      linarith)
  have hcompact : IsCompact (closure (Set.range u)) :=
    isCompact_iff_totallyBounded_isComplete.mpr ⟨htb.closure, isClosed_closure.isComplete⟩
  obtain ⟨x, _, a, ha, hlim⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self n))
  exact hn ⟨a, x, ha, hlim⟩

private theorem weakDual_mem_closure_of_finite_agreement (A : Set (WeakDual ℝ E))
    (φ : WeakDual ℝ E)
    (h : ∀ s : Finset E, ∃ ψ ∈ A, ∀ x ∈ s, ψ x = φ x) : φ ∈ closure A := by
  rw [mem_closure_iff_nhds]
  intro U hU
  have hEmb : Topology.IsEmbedding (fun θ : WeakDual ℝ E => (θ : E → ℝ)) :=
    WeakBilin.isEmbedding (by
      intro a b hab
      apply ContinuousLinearMap.ext
      intro x
      simpa only [topDualPairing_apply] using
        congrArg (fun l : E →ₗ[ℝ] ℝ => l x) hab)
  rw [hEmb.isInducing.nhds_eq_comap φ] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
  rw [nhds_pi] at hV
  have hV' : V ∈ Filter.pi (fun x : E => pure (φ x)) :=
    Filter.pi_mono (fun x => pure_le_nhds (φ x)) hV
  obtain ⟨I, hI, hIV⟩ := Filter.mem_pi_pure.mp hV'
  obtain ⟨ψ, hψ, hagree⟩ := h hI.toFinset
  exact ⟨ψ, hVU (hIV (fun x => ψ x) (fun x hx => hagree x (hI.mem_toFinset.mpr hx))), hψ⟩

private theorem dual_adjust_annihilate (M : Submodule ℝ E) [FiniteDimensional ℝ M]
    (u : E) (φ : Dual E) {ε : ℝ} (hε : 0 < ε)
    (hu : ε < Metric.infDist u (M : Set E)) :
    ∃ ψ : Dual E, (∀ x ∈ M, ψ x = φ x) ∧ ψ u = 0 ∧
      ‖ψ‖ ≤ ‖φ‖ + ‖φ‖ * ‖u‖ / ε := by
  have : IsClosed (M : Set E) := M.closed_of_finiteDimensional
  let d := ‖M.mkQ u‖
  have hd : ε < d := by
    have heq : d = Metric.infDist u (M : Set E) :=
      QuotientAddGroup.norm_mk (S := M.toAddSubgroup) u
    rwa [heq]
  obtain ⟨l, hl, hlu⟩ := exists_dual_vector'' ℝ (M.mkQ u)
  let θ : Dual E := l.comp M.mkQL
  have hθu : θ u = d := hlu
  have hθM (x : E) (hx : x ∈ M) : θ x = 0 := by
    change l (M.mkQ x) = 0
    rw [show M.mkQ x = 0 from (Submodule.Quotient.mk_eq_zero M).mpr hx, map_zero]
  have hθnorm : ‖θ‖ ≤ 1 := by
    apply θ.opNorm_le_bound zero_le_one
    intro x
    calc
      ‖θ x‖ ≤ ‖l‖ * ‖M.mkQ x‖ := l.le_opNorm _
      _ ≤ 1 * ‖x‖ := mul_le_mul hl (Submodule.Quotient.norm_mk_le M x)
        (norm_nonneg _) zero_le_one
  refine ⟨φ - (φ u / d) • θ, ?_, ?_, ?_⟩
  · intro x hx
    simp [hθM x hx]
  · simp [hθu, (hε.trans hd).ne']
  · calc
      ‖φ - (φ u / d) • θ‖ ≤ ‖φ‖ + ‖(φ u / d) • θ‖ := norm_sub_le _ _
      _ ≤ ‖φ‖ + |φ u| / d := by
        rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (hε.trans hd)]
        exact add_le_add le_rfl (mul_le_of_le_one_right
          (div_nonneg (abs_nonneg _) (hε.trans hd).le) hθnorm)
      _ ≤ ‖φ‖ + ‖φ‖ * ‖u‖ / ε := by
        gcongr
        exact φ.le_opNorm u

/-- Proposition 3.2 (`prop:noncompact-minima`): for a bounded sequence with no
norm-convergent subsequence, the finite minima of the absolute evaluations decrease
to zero in `Free p E`. The minimum at index n uses the first n + 1 vectors. This is
the complete result underlying the introductory noncompactness observation. -/
theorem noncompact_minima [CompleteSpace E] (p : Exponent) (u : ℕ → E)
    (hu : Bornology.IsBounded (Set.range u))
    (hn : ¬ ∃ (a : ℕ → ℕ) (x : E), StrictMono a ∧
      Tendsto (u ∘ a) atTop (𝓝 x)) : DecreasesToZero (evaluationMinima p u) := by
  classical
  obtain ⟨ε, hε, hescape⟩ := finite_dimensional_escape u hu hn
  obtain ⟨C, hC⟩ := hu.exists_norm_le
  have hCpos : 0 ≤ C := (norm_nonneg (u 0)).trans (hC _ (Set.mem_range_self 0))
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro m n hmn
    apply Finset.le_inf'
    intro i _
    exact Finset.inf'_le (fun j : Fin (n + 1) => |delta p (u j)|)
      (Finset.mem_univ (⟨i, lt_of_lt_of_le i.isLt (Nat.add_le_add_right hmn 1)⟩ : Fin (n + 1)))
  · rintro _ ⟨n, rfl⟩
    exact Finset.le_inf' _ _ (fun _ _ => abs_nonneg _)
  · intro g hg
    have hgabs (φ : Dual E) (n : ℕ) : g φ ≤ |φ (u n)| := by
      have hgn := (hg (Set.mem_range_self n)).trans
        (Finset.inf'_le (fun j : Fin (n + 1) => |delta p (u j)|)
          (Finset.mem_univ (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))))
      exact (free_le_iff p _ _).mp hgn φ
    apply (free_le_iff p _ _).mpr
    intro φ
    let R : ℝ := ‖φ‖ + ‖φ‖ * C / ε
    let A : Set (WeakDual ℝ E) := {ψ | ‖ψ.toStrongDual‖ ≤ R ∧ ∃ n, ψ (u n) = 0}
    have hφR : ‖φ‖ ≤ R := le_add_of_nonneg_right (by positivity)
    have hclosure : StrongDual.toWeakDual φ ∈ closure A := by
      apply weakDual_mem_closure_of_finite_agreement
      intro s
      let M : Submodule ℝ E := Submodule.span ℝ (s : Set E)
      let : FiniteDimensional ℝ M := FiniteDimensional.span_finset ℝ s
      obtain ⟨n, hn⟩ := hescape M inferInstance
      obtain ⟨ψ, hagree, hzero, hnorm⟩ := dual_adjust_annihilate M (u n) φ hε hn
      refine ⟨StrongDual.toWeakDual ψ, ⟨?_, n, hzero⟩, ?_⟩
      · exact hnorm.trans (by dsimp [R]; gcongr; exact hC _ (Set.mem_range_self n))
      · intro x hx
        exact hagree x (Submodule.subset_span hx)
    exact ContinuousWithinAt.closure_le
      (f := fun ψ : WeakDual ℝ E => g (WeakDual.toStrongDual ψ))
      (g := fun _ : WeakDual ℝ E => (0 : ℝ)) hclosure
      (((weakStar_continuous_bounded p g R) _ hφR).mono (fun _ h => h.1))
      continuousWithinAt_const (fun ψ ⟨_, n, hn⟩ => by
        simpa only [WeakDual.toStrongDual_apply, hn, abs_zero] using hgabs ψ.toStrongDual n)

private theorem exists_unit_image_small (T : F →L[ℝ] E) (hT : ¬ BoundedBelow T)
    {c : ℝ} (hc : 0 < c) : ∃ x : F, ‖x‖ = 1 ∧ ‖T x‖ < c := by
  have hbad : ¬ ∀ x, c * ‖x‖ ≤ ‖T x‖ := fun h => hT ⟨c, hc, h⟩
  obtain ⟨x, hx⟩ := not_forall.mp hbad
  have hxlt := lt_of_not_ge hx
  have hnx : 0 < ‖x‖ := by
    by_contra! hn
    have hz : x = 0 := norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
    simp [hz] at hxlt
  refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnx), inv_mul_cancel₀ hnx.ne']
  · rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnx)]
    exact (inv_mul_lt_iff₀ hnx).mpr (by simpa [mul_comm] using hxlt)

/-- Proposition 1.2 (`prop:necessary`): an operator between Banach spaces whose induced
free-lattice map is order continuous must be zero or bounded below. The proof combines
injectivity with the noncompact-minima witness to exclude an unbounded inverse on the range. -/
theorem necessary [CompleteSpace F] (p : Exponent) (T : F →L[ℝ] E)
    (h : IsOrderContinuousOp (induced p T).toContinuousLinearMap.toLinearMap) :
    T = 0 ∨ BoundedBelow T := by
  classical
  by_cases hT : T = 0
  · exact Or.inl hT
  right
  by_contra hb
  have hinj := injectivity p T hT h
  obtain ⟨v, hv⟩ : ∃ v, T v ≠ 0 := by
    by_contra! hz
    exact hT (ContinuousLinearMap.ext hz)
  let c (n : ℕ) : ℝ := ‖T v‖ / 4 * (1 / 2 : ℝ) ^ n
  have hc (n : ℕ) : 0 < c n := by dsimp [c]; positivity
  choose x hxnorm hxsmall using (fun n => exists_unit_image_small T hb (hc n))
  have hcsum : Summable c := summable_geometric_two.mul_left _
  have hclim : Tendsto c atTop (𝓝 0) := hcsum.tendsto_atTop_zero
  have hTx : Tendsto (fun n => T (x n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hxsmall n).le) hclim
  let u (n : ℕ) := v + x n
  have hu : Bornology.IsBounded (Set.range u) := by
    apply isBounded_iff_forall_norm_le.mpr
    exact ⟨‖v‖ + 1, by rintro _ ⟨n, rfl⟩; exact (norm_add_le _ _).trans_eq (by rw [hxnorm])⟩
  have hn : ¬ ∃ (a : ℕ → ℕ) (w : F), StrictMono a ∧ Tendsto (u ∘ a) atTop (𝓝 w) := by
    rintro ⟨a, w, ha, haw⟩
    have hxa : Tendsto (x ∘ a) atTop (𝓝 (w - v)) := by
      simpa only [u, Function.comp_def, add_sub_cancel_left] using haw.sub_const v
    have hnorm : ‖w - v‖ = 1 := tendsto_nhds_unique hxa.norm
      (by simpa only [Function.comp_def, hxnorm] using (tendsto_const_nhds (x := (1 : ℝ))))
    have hzero : T (w - v) = 0 := tendsto_nhds_unique (T.continuous.tendsto _ |>.comp hxa)
      (hTx.comp ha.tendsto_atTop)
    have hw : w - v = 0 := hinj (hzero.trans (map_zero T).symm)
    simp [hw] at hnorm
  have hf := noncompact_minima p u hu hn
  let z (n : ℕ) : Free p E := |delta p (T (x n))|
  have hzc (n : ℕ) : ‖z n‖ ≤ c n := by
    simpa only [z, norm_abs_eq_norm, LinearIsometry.norm_map] using (hxsmall n).le
  have hzsum : Summable z := hcsum.of_norm_bounded hzc
  let e : Free p E := ∑' n, z n
  have hepos : 0 ≤ e := tsum_nonneg (fun n => abs_nonneg _)
  have hze (n : ℕ) : z n ≤ e := hzsum.le_tsum n (fun _ _ => abs_nonneg _)
  have hcnorm : HasSum c (‖T v‖ / 2) := by
    have heq : ‖T v‖ / 4 * (∑' n : ℕ, (1 / 2 : ℝ) ^ n) = ‖T v‖ / 2 := by
      rw [tsum_geometric_two]
      ring
    exact heq ▸ summable_geometric_two.hasSum.mul_left (‖T v‖ / 4)
  have henorm : ‖e‖ ≤ ‖T v‖ / 2 := tsum_of_norm_bounded hcnorm hzc
  let g : Free p E := |delta p (T v)| - e
  have hbound (n : ℕ) : g ≤ induced p T (evaluationMinima p u n) := by
    change g ≤ (induced p T).toVecLatHom
      (Finset.univ.inf' Finset.univ_nonempty (fun i : Fin (n + 1) => |delta p (u i)|))
    rw [map_finset_inf']
    apply Finset.le_inf'
    intro i _
    apply (free_le_iff p _ _).mpr
    intro φ
    change |φ (T v)| - e φ ≤ |φ (T (v + x i))|
    have hzei := (free_le_iff p _ _).mp (hze i) φ
    change |φ (T (x i))| ≤ e φ at hzei
    rw [map_add, map_add]
    have htriangle := abs_add_le (φ (T v) + φ (T (x i))) (-φ (T (x i)))
    simp only [add_neg_cancel_right, abs_neg] at htriangle
    linarith
  have hcimage := orderContinuous_sigmaOrderContinuous _
    (fun _ h => (induced p T).toVecLatHom.map_nonneg h) h _ hf
  have hgle : g ≤ 0 := hcimage.2.2 (by rintro _ ⟨n, rfl⟩; exact hbound n)
  have hdle : |delta p (T v)| ≤ e := sub_nonpos.mp hgle
  have hnormle : ‖T v‖ ≤ ‖e‖ := by
    simpa only [abs_abs, abs_of_nonneg hepos, LinearIsometry.norm_map] using
      (norm_le_norm_of_abs_le_abs (a := delta p (T v)) (b := e)
        (by simpa only [abs_of_nonneg hepos] using hdle))
  exact (norm_pos_iff.mpr hv).not_ge (by linarith)

/-- The support function of a norm-compact set, used for the endpoint minorant. -/
def compactSupport (K : Set E) (φ : Dual E) : ℝ :=
  sSup ((fun x => |φ x|) '' K)

private theorem compactSupport_homogeneous (K : Set E) :
    PosHomogeneous (compactSupport K) := by
  intro a ha φ
  unfold compactSupport
  simp only [smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ha]
  simpa only [← Set.image_smul, Set.image_image, smul_eq_mul, Function.comp_def] using
    Real.sSup_smul_of_nonneg ha ((fun x => |φ x|) '' K)

private theorem compactSupport_continuous {K : Set E} (hK : IsCompact K) :
    WeakStarContinuousOnBall (compactSupport K) := by
  apply hK.continuous_sSup
  apply Continuous.abs
  apply continuous_prod_of_continuous_lipschitzWith' _ 1
  · intro φ
    exact φ.1.toStrongDual.lipschitzWith.weaken (by
      have h : ‖φ.1.toStrongDual‖ ≤ 1 := by
        simpa only [FVLv.dualUnitBall, Set.mem_preimage, Metric.mem_closedBall,
          dist_zero_right] using φ.2
      exact_mod_cast h)
  · intro x
    exact (WeakDual.eval_continuous x).comp continuous_subtype_val

private theorem compactSupport_le {K : Set E} (hK : IsCompact K)
    (φ : Dual E) {x : E} (hx : x ∈ K) : |φ x| ≤ compactSupport K φ :=
  le_csSup (hK.bddAbove_image φ.continuous.abs.continuousOn) (mem_image_of_mem _ hx)

private theorem compactSupport_nonneg {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (φ : Dual E) : 0 ≤ compactSupport K φ := by
  obtain ⟨x, hx⟩ := hne
  exact (abs_nonneg _).trans (compactSupport_le hK φ hx)

private theorem weakDualNormBall_closed (R : ℝ) :
    IsClosed (weakDualNormBall (E := E) R) := by
  convert WeakDual.isClosed_closedBall (0 : Dual E) R using 1
  ext φ
  simp [weakDualNormBall, Metric.mem_closedBall, dist_zero_right]

private theorem weakDualNormBall_compact (R : ℝ) :
    IsCompact (weakDualNormBall (E := E) R) := by
  convert WeakDual.isCompact_closedBall (0 : Dual E) R using 1
  ext φ
  simp [weakDualNormBall, Metric.mem_closedBall, dist_zero_right]

private theorem boundedBelow_dual_lift [CompleteSpace E] [CompleteSpace F]
    (T : F →L[ℝ] E) (hT : BoundedBelow T) :
    ∃ C > 0, ∀ ψ : Dual F, ∃ φ : Dual E, φ.comp T = ψ ∧ ‖φ‖ ≤ C * ‖ψ‖ := by
  obtain ⟨hi, hc⟩ := (embedding_iff T).mp hT
  let R : T.range →L[ℝ] F := (T.equivRange hi hc).symm.toContinuousLinearMap
  refine ⟨‖R‖ + 1, by positivity, fun ψ => ?_⟩
  obtain ⟨φ, hφ, hn⟩ := exists_extension_norm_eq T.range (ψ.comp R)
  refine ⟨φ, ?_, ?_⟩
  · ext x
    change φ (T x) = ψ x
    rw [hφ ⟨T x, ⟨x, rfl⟩⟩]
    change ψ (R ⟨T x, ⟨x, rfl⟩⟩) = ψ x
    rw [show R ⟨T x, ⟨x, rfl⟩⟩ = x from T.equivRange_symm_apply hi hc x]
  · calc
      ‖φ‖ = ‖ψ.comp R‖ := hn
      _ ≤ ‖ψ‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖R‖ + 1) * ‖ψ‖ := by nlinarith [norm_nonneg ψ]

/-- A bounded lift of every dual functional transfers closedness on norm balls. -/
private theorem weakDual_closed_of_pullback [CompleteSpace E] [CompleteSpace F]
    (T : F →L[ℝ] E) (hT : BoundedBelow T) (D : Set (WeakDual ℝ F))
    (hD : ∀ r : ℝ, IsClosed
      ({φ : WeakDual ℝ E | StrongDual.toWeakDual (φ.toStrongDual.comp T) ∈ D} ∩
        weakDualNormBall r)) :
    ∀ r : ℝ, IsClosed (D ∩ weakDualNormBall r) := by
  obtain ⟨C, hC, hlift⟩ := boundedBelow_dual_lift T hT
  let R : WeakDual ℝ E → WeakDual ℝ F :=
    fun φ => StrongDual.toWeakDual (φ.toStrongDual.comp T)
  have hR : Continuous R := WeakDual.continuous_of_continuous_eval
    (fun x => WeakDual.eval_continuous (T x))
  intro r
  have heq : D ∩ weakDualNormBall r =
      R '' ((R ⁻¹' D) ∩ weakDualNormBall (C * max r 0)) ∩ weakDualNormBall r := by
    ext ψ
    constructor
    · rintro ⟨hψ, hn⟩
      obtain ⟨φ, hφ, hφn⟩ := hlift ψ.toStrongDual
      refine ⟨⟨StrongDual.toWeakDual φ, ⟨?_, ?_⟩, ?_⟩, hn⟩
      · change StrongDual.toWeakDual (φ.comp T) ∈ D
        rwa [hφ]
      · exact hφn.trans (mul_le_mul_of_nonneg_left (hn.trans (le_max_left _ _)) hC.le)
      · exact congrArg StrongDual.toWeakDual hφ
    · rintro ⟨⟨φ, ⟨hφ, _⟩, rfl⟩, hn⟩
      exact ⟨hφ, hn⟩
  rw [heq]
  exact ((weakDualNormBall_compact (C * max r 0)).of_isClosed_subset
    (hD _) inter_subset_right).image hR |>.isClosed.inter (weakDualNormBall_closed r)

/-- The image of a positive patch contains a compact-convergence neighborhood. -/
private theorem dual_patch_compact [CompleteSpace E] [CompleteSpace F]
    (T : F →L[ℝ] E) (hT : BoundedBelow T) (p : Exponent) (g : Free p E)
    (φ₀ : Dual E) (ε : ℝ) (hε : ε < g φ₀) :
    ∃ K : Set F, IsCompact K ∧ K.Nonempty ∧ ∀ ψ : Dual F,
      (∀ x ∈ K, |(ψ - φ₀.comp T) x| ≤ 1) →
      ∃ φ : Dual E, φ.comp T = ψ ∧ ε < g φ := by
  let D : Set (WeakDual ℝ F) := {ψ | ∀ φ : Dual E,
    φ.comp T = ψ.toStrongDual + φ₀.comp T → g φ ≤ ε}
  have hD : ∀ r : ℝ, IsClosed (D ∩ weakDualNormBall r) := by
    apply weakDual_closed_of_pullback T hT
    intro r
    let Z := {z : Dual E // z.comp T = 0}
    let : Nonempty Z := ⟨⟨0, by simp⟩⟩
    have hset : {φ : WeakDual ℝ E | StrongDual.toWeakDual (φ.toStrongDual.comp T) ∈ D} ∩
        weakDualNormBall r =
        ⋂ z : Z, {φ : WeakDual ℝ E | g (φ.toStrongDual + φ₀ + z.1) ≤ ε} ∩
          weakDualNormBall r := by
      ext φ
      simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter]
      constructor
      · rintro ⟨hφ, hn⟩ z
        refine ⟨hφ (φ.toStrongDual + φ₀ + z.1) ?_, hn⟩
        simp only [ContinuousLinearMap.add_comp, z.2, add_zero]
        rfl
      · intro hφ
        refine ⟨?_, (hφ (Classical.choice inferInstance)).2⟩
        intro η hη
        change η.comp T = φ.toStrongDual.comp T + φ₀.comp T at hη
        have hz : (η - φ.toStrongDual - φ₀).comp T = 0 := by
          rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.sub_comp, hη]
          abel
        have hh := (hφ ⟨η - φ.toStrongDual - φ₀, hz⟩).1
        have heq : φ.toStrongDual + φ₀ + (η - φ.toStrongDual - φ₀) = η := by abel
        exact heq ▸ hh
    rw [hset]
    apply isClosed_iInter
    intro z
    have hc : ContinuousOn (fun φ : WeakDual ℝ E => g (φ.toStrongDual + (φ₀ + z.1)))
        (weakDualNormBall r) := by
      have ht : ContinuousOn (fun φ : WeakDual ℝ E =>
          φ + StrongDual.toWeakDual (φ₀ + z.1)) (weakDualNormBall r) :=
        (continuous_id.add continuous_const).continuousOn
      have hh := (weakStar_continuous_bounded p g (r + ‖φ₀ + z.1‖)).comp ht (by
        intro φ hφ
        exact (norm_add_le _ _).trans (add_le_add hφ le_rfl))
      exact hh
    simpa only [add_assoc, Set.ofPred_and, Set.ofPred_mem_eq, inter_comm] using
      (weakDualNormBall_closed (E := E) r).isClosed_le hc continuousOn_const
  have h0 : (0 : WeakDual ℝ F) ∉ D := by
    intro h
    exact hε.not_ge (h φ₀ (by simp))
  obtain ⟨K, hK, hsep⟩ := weakDual_exists_compact_separator D hD h0
  refine ⟨insert 0 K, hK.insert 0, Set.insert_nonempty _ _, fun ψ hψ => ?_⟩
  have hn : StrongDual.toWeakDual (ψ - φ₀.comp T) ∉ D := by
    intro hd
    obtain ⟨x, hx, hgt⟩ := hsep _ hd
    exact hgt.not_ge (hψ x (mem_insert_of_mem _ hx))
  change ¬ (∀ φ : Dual E, φ.comp T = (ψ - φ₀.comp T) + φ₀.comp T → g φ ≤ ε) at hn
  rw [sub_add_cancel] at hn
  push Not at hn
  exact hn

/-- Homogenize a compact-convergence patch to obtain a nonzero free-lattice minorant. -/
private theorem compact_patch_minorant {K : Set F} (hK : IsCompact K)
    (hKne : K.Nonempty) (ψ₀ : Dual F) (e : F) (he : ψ₀ e = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : Free Exponent.infinity F, 0 < a ψ₀ ∧ ∀ f : Free Exponent.infinity F,
      0 ≤ f → (∀ ψ : Dual F, (∀ x ∈ K, |(ψ - ψ₀) x| ≤ 1) → ε ≤ f ψ) → a ≤ f := by
  let Q : F →L[ℝ] F := ContinuousLinearMap.id ℝ F - ψ₀.smulRight e
  let L := Q '' K
  have hL : IsCompact L := hK.image Q.continuous
  have hLne : L.Nonempty := hKne.image Q
  obtain ⟨s, hs⟩ := (infinity_representation (compactSupport L)).mpr
    ⟨compactSupport_homogeneous L, compactSupport_continuous hL⟩
  let a : Free Exponent.infinity F := ε • ((delta Exponent.infinity e - s) ⊔ 0)
  have hval (ψ : Dual F) : a ψ = ε * max (ψ e - compactSupport L ψ) 0 := by
    change ε * max (ψ e - s ψ) 0 = _
    rw [hs]
  have hs₀ : compactSupport L ψ₀ = 0 := by
    apply le_antisymm
    · apply csSup_le (hLne.image _)
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      simp [Q, he]
    · exact compactSupport_nonneg hL hLne ψ₀
  refine ⟨a, ?_, fun f hf hpatch => ?_⟩
  · simpa [hval, he, hs₀] using hε
  · apply (free_le_iff Exponent.infinity _ _).mpr
    intro ψ
    rw [hval]
    by_cases hpos : 0 < ψ e - compactSupport L ψ
    · have hspos := compactSupport_nonneg hL hLne ψ
      have ht : 0 < ψ e := by linarith
      have hpatch' : ε ≤ f ((ψ e)⁻¹ • ψ) := by
        apply hpatch
        intro x hx
        have hb := compactSupport_le hL ψ (mem_image_of_mem Q hx)
        have heq : (((ψ e)⁻¹ • ψ) - ψ₀) x = (ψ e)⁻¹ * ψ (Q x) := by
          simp only [Q, sub_apply, ContinuousLinearMap.id_apply,
            ContinuousLinearMap.smulRight_apply, map_sub, map_smul, smul_apply, smul_eq_mul]
          field_simp
        rw [heq, abs_mul, abs_of_pos (inv_pos.mpr ht)]
        exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ht.le)).trans
          ((inv_mul_le_one₀ ht).mpr (by linarith))
      have hhom := f.1.2.1 ((ψ e)⁻¹) (inv_nonneg.mpr ht.le) ψ
      have hbound : ε * ψ e ≤ f ψ := by
        rw [hhom] at hpatch'
        have hh := mul_le_mul_of_nonneg_left hpatch' ht.le
        simpa only [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul, mul_comm (ψ e) ε] using hh
      rw [max_eq_left hpos.le]
      exact (mul_le_mul_of_nonneg_left (by linarith) hε.le).trans hbound
    · rw [max_eq_right (le_of_not_gt hpos), mul_zero]
      exact (free_le_iff Exponent.infinity _ _).mp hf ψ

private theorem induced_infinity_orderContinuous_of_boundedBelow
    [CompleteSpace E] [CompleteSpace F] (T : F →L[ℝ] E) (hT : BoundedBelow T) :
    IsOrderContinuousOp (induced Exponent.infinity T).toContinuousLinearMap.toLinearMap := by
  let S := induced Exponent.infinity T
  apply (orderContinuous_iff_decreasing S.toContinuousLinearMap.toLinearMap
    (fun _ h => S.toVecLatHom.map_nonneg h)).mpr
  intro ι _ _ _ f hf
  refine ⟨S.toVecLatHom.monotone.comp_antitone hf.1, ⟨?_, ?_⟩⟩
  · rintro _ ⟨i, rfl⟩
    exact S.toVecLatHom.map_nonneg (hf.2.1 ⟨i, rfl⟩)
  · intro g hg
    apply (free_le_iff Exponent.infinity _ _).mpr
    intro φ₀
    change g φ₀ ≤ 0
    by_contra hn
    have hgpos : 0 < g φ₀ := lt_of_not_ge hn
    let ψ₀ := φ₀.comp T
    have hψ₀ : ψ₀ ≠ 0 := by
      intro hzero
      let i : ι := Classical.choice inferInstance
      have hh := (free_le_iff Exponent.infinity _ _).mp (hg ⟨i, rfl⟩) φ₀
      change g φ₀ ≤ f i ψ₀ at hh
      rw [hzero] at hh
      have hfzero : f i (0 : Dual F) = 0 := by
        simpa using (f i).1.2.1 0 le_rfl (0 : Dual F)
      exact hgpos.not_ge (hh.trans_eq hfzero)
    obtain ⟨x, hx⟩ : ∃ x : F, ψ₀ x ≠ 0 := by
      by_contra h
      apply hψ₀
      ext x
      simpa using not_exists.mp h x
    let e := (ψ₀ x)⁻¹ • x
    have he : ψ₀ e = 1 := by simp [e, hx]
    obtain ⟨K, hK, hKne, hpatch⟩ := dual_patch_compact T hT Exponent.infinity g
      φ₀ (g φ₀ / 2) (by linarith)
    obtain ⟨a, hapos, ha⟩ := compact_patch_minorant hK hKne ψ₀ e he
      (g φ₀ / 2) (by positivity)
    have halower : a ∈ lowerBounds (Set.range f) := by
      rintro _ ⟨i, rfl⟩
      apply ha (f i) (hf.2.1 ⟨i, rfl⟩)
      intro ψ hψ
      obtain ⟨φ, hφ, hφg⟩ := hpatch ψ hψ
      have hh := (free_le_iff Exponent.infinity _ _).mp (hg ⟨i, rfl⟩) φ
      change g φ ≤ f i (φ.comp T) at hh
      rw [hφ] at hh
      exact hφg.le.trans hh
    have ha0 := (free_le_iff Exponent.infinity _ _).mp (hf.2.2 halower) ψ₀
    exact hapos.not_ge ha0

/-- Theorem 1.1 (`thm:intro-infty`): at exponent ∞, the induced map is order continuous
if and only if the original operator is zero or bounded below. The endpoint representation
and Hahn–Banach extension provide the converse to `necessary`. -/
theorem intro_infty [CompleteSpace E] [CompleteSpace F] (T : F →L[ℝ] E) :
    IsOrderContinuousOp (induced Exponent.infinity T).toContinuousLinearMap.toLinearMap ↔
      T = 0 ∨ BoundedBelow T := by
  constructor
  · exact necessary Exponent.infinity T
  · rintro (hzero | hT)
    · have hz := (induced_eq_zero_iff Exponent.infinity T).mpr hzero
      intro ι _ _ _ x a _
      change OrderConvergesTo
        (fun i => (induced Exponent.infinity T).toContinuousLinearMap (x i))
        ((induced Exponent.infinity T).toContinuousLinearMap a)
      simpa only [hz, zero_apply] using
        (orderConvergesTo_const (ι := ι) (0 : Free Exponent.infinity E))
    · exact induced_infinity_orderContinuous_of_boundedBelow T hT

section Algebraic
variable (V : Type u) (W : Type v)
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Section 2: the algebraic-dual functional model, without a norm on the generator space. -/
def algebraicFreeSublattice : VectorSublattice ((V →ₗ[ℝ] ℝ) → ℝ) :=
  VectorSublattice.generated (Set.range (fun x : V => fun φ : V →ₗ[ℝ] ℝ => φ x))

/-- The algebraic free vector lattice over a real vector space V, realized as the lattice
generated by evaluations on its algebraic dual. No norm or completeness assumption on V
is used; `algebraic_normed_identification` connects this model to BanLat when V is normed. -/
abbrev AlgebraicFVL : Type u := algebraicFreeSublattice V

theorem algebraic_precomp_mem (T : V →ₗ[ℝ] W) (f : AlgebraicFVL V) :
    (fun φ : W →ₗ[ℝ] ℝ => f.1 (φ.comp T)) ∈ algebraicFreeSublattice W := by
  let C : VectorSublattice ((V →ₗ[ℝ] ℝ) → ℝ) :=
    { carrier := {g | (fun φ : W →ₗ[ℝ] ℝ => g (φ.comp T)) ∈ algebraicFreeSublattice W}
      zero_mem' := (algebraicFreeSublattice W).zero_mem
      add_mem' := fun hg hh => (algebraicFreeSublattice W).add_mem hg hh
      smul_mem' := fun r _ hg => (algebraicFreeSublattice W).smul_mem r hg
      sup_mem' := fun hg hh => (algebraicFreeSublattice W).sup_mem hg hh }
  apply VectorSublattice.generated_le (Y := C) _ f.2
  rintro _ ⟨x, rfl⟩
  exact VectorSublattice.subset_generated _ ⟨T x, rfl⟩

/-- Equation (2.6) (`eq:fvl-composition`): composition with the algebraic adjoint. -/
def algebraicInduced (T : V →ₗ[ℝ] W) : VecLatHom (AlgebraicFVL V) (AlgebraicFVL W) where
  toFun f := ⟨fun φ => f.1 (φ.comp T), algebraic_precomp_mem V W T f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

/-- Section 2: canonical evaluation for the algebraic free vector lattice. -/
def algebraicDelta (V : Type u) [AddCommGroup V] [Module ℝ V] :
    V →ₗ[ℝ] AlgebraicFVL V where
  toFun x := ⟨fun φ => φ x, VectorSublattice.subset_generated _ ⟨x, rfl⟩⟩
  map_add' x y := Subtype.ext (funext fun φ => map_add φ x y)
  map_smul' r x := Subtype.ext (funext fun φ => map_smul φ r x)

/-- Equation (2.6) on the canonical algebraic generators. -/
theorem algebraicInduced_delta (V : Type u) (W : Type v)
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (T : V →ₗ[ℝ] W) (x : V) :
    algebraicInduced V W T (algebraicDelta V x) = algebraicDelta W (T x) := rfl

private theorem algebraic_apply_zero (f : AlgebraicFVL V) : f.1 0 = 0 := by
  let C : VectorSublattice ((V →ₗ[ℝ] ℝ) → ℝ) :=
    { carrier := {g | g 0 = 0}
      zero_mem' := rfl
      add_mem' := fun {g h} hg hh => by change g 0 + h 0 = 0; rw [hg, hh, add_zero]
      smul_mem' := fun r g hg => by change r * g 0 = 0; rw [hg, mul_zero]
      sup_mem' := fun {g h} hg hh => by change g 0 ⊔ h 0 = 0; rw [hg, hh, sup_idem] }
  apply VectorSublattice.generated_le (Y := C) _ f.2
  rintro _ ⟨x, rfl⟩
  rfl

private theorem algebraic_continuous_line (f : AlgebraicFVL V) (φ ψ : V →ₗ[ℝ] ℝ) :
    Continuous (fun t : ℝ => f.1 (φ + t • ψ)) := by
  let C : VectorSublattice ((V →ₗ[ℝ] ℝ) → ℝ) :=
    { carrier := {g | Continuous (fun t : ℝ => g (φ + t • ψ))}
      zero_mem' := continuous_const
      add_mem' := fun hg hh => hg.add hh
      smul_mem' := fun r _ hg => continuous_const.smul hg
      sup_mem' := fun hg hh => hg.sup hh }
  apply VectorSublattice.generated_le (Y := C) _ f.2
  rintro _ ⟨x, rfl⟩
  exact continuous_const.add (continuous_id.mul_const (ψ x))

private theorem algebraic_collision_decreasesToZero (x y : V) (hne : x ≠ y) :
    DecreasesToZero (fun n : ℕ =>
      (|algebraicDelta V x + algebraicDelta V y| -
        (n + 1 : ℝ) • |algebraicDelta V x - algebraicDelta V y|) ⊔ 0) := by
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro m n hmn φ
    change max (|φ x + φ y| - (n + 1 : ℝ) * |φ x - φ y|) 0 ≤
      max (|φ x + φ y| - (m + 1 : ℝ) * |φ x - φ y|) 0
    exact max_le_max_right 0 (by gcongr)
  · rintro _ ⟨n, rfl⟩
    exact le_sup_right
  · intro g hg
    let b : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun φ => φ (x - y)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hb : b ≠ 0 := by
      obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℝ (sub_ne_zero.mpr hne)
      intro h
      exact one_ne_zero (hφ.symm.trans (DFunLike.congr_fun h φ))
    intro φ
    apply nonpos_of_nonpos_off_kernel b hb g.1 (algebraic_continuous_line V g) _ φ
    intro ψ hψ
    apply collision_scalar_nonpos (a := ψ x + ψ y) (b := ψ x - ψ y)
      (by simpa only [b, LinearMap.coe_mk, AddHom.coe_mk, map_sub] using hψ)
    intro n
    exact hg ⟨n, rfl⟩ ψ

private theorem linear_leftInverse_preserving (T : V →ₗ[ℝ] W) (hT : Function.Injective T)
    (φ : W →ₗ[ℝ] ℝ) (e : V) (he : φ (T e) = 1) :
    ∃ Q : W →ₗ[ℝ] V, Q.comp T = LinearMap.id ∧ (φ.comp T).comp Q = φ := by
  obtain ⟨R, hR⟩ := T.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hT)
  have hR' (x : V) : R (T x) = x := DFunLike.congr_fun hR x
  refine ⟨R + (φ - (φ.comp T).comp R).smulRight e, ?_, ?_⟩
  · ext x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
      LinearMap.sub_apply, hR', sub_self, zero_smul, add_zero, LinearMap.id_apply]
  · ext x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
      LinearMap.sub_apply, map_add, map_smul, he, smul_eq_mul, mul_one, add_sub_cancel]

/-- Injective linear maps induce order-continuous maps of the algebraic free lattices. -/
theorem algebraicInduced_orderContinuous_of_injective (T : V →ₗ[ℝ] W)
    (hT : Function.Injective T) : IsOrderContinuousOp (algebraicInduced V W T).toLinearMap := by
  let S := algebraicInduced V W T
  apply (orderContinuous_iff_decreasing S.toLinearMap (fun _ h => S.map_nonneg h)).2
  intro ι _ _ _ x hx
  refine ⟨S.monotone.comp_antitone hx.1, ⟨?_, ?_⟩⟩
  · rintro _ ⟨i, rfl⟩
    exact S.map_nonneg (hx.2.1 ⟨i, rfl⟩)
  · intro g hg
    change ∀ φ : W →ₗ[ℝ] ℝ, g.1 φ ≤ 0
    intro φ
    by_cases hφ : φ.comp T = 0
    · obtain ⟨i⟩ := ‹Nonempty ι›
      have hi := hg (Set.mem_range_self i)
      have hiφ : g.1 φ ≤ (x i).1 (φ.comp T) := hi φ
      simpa only [hφ, algebraic_apply_zero] using hiφ
    · obtain ⟨v, hv⟩ : ∃ v, φ (T v) ≠ 0 := by
        by_contra! h
        exact hφ (LinearMap.ext h)
      obtain ⟨Q, hQT, hφQ⟩ := linear_leftInverse_preserving V W T hT φ
        ((φ (T v))⁻¹ • v) (by simp [map_smul, hv])
      have hlower : algebraicInduced W V Q g ≤ 0 := hx.2.2 (by
        rintro _ ⟨i, rfl⟩
        intro ψ
        change g.1 (ψ.comp Q) ≤ (x i).1 ψ
        have hi := hg (Set.mem_range_self i) (ψ.comp Q)
        change g.1 (ψ.comp Q) ≤ (x i).1 ((ψ.comp Q).comp T) at hi
        simpa only [LinearMap.comp_assoc, hQT, LinearMap.comp_id] using hi)
      have hf := hlower (φ.comp T)
      change g.1 ((φ.comp T).comp Q) ≤ 0 at hf
      simpa only [hφQ] using hf

/-- Lemma 2.6 (`lem:regular-inclusion`): the inclusion of a vector subspace induces an
order-continuous map of algebraic free vector lattices. This uses only linear algebra,
with no norm, topology, or closedness condition on the subspace. -/
theorem regular_inclusion (M : Submodule ℝ V) :
    IsOrderContinuousOp (algebraicInduced M V M.subtype).toLinearMap :=
  algebraicInduced_orderContinuous_of_injective M V M.subtype Subtype.val_injective

/-- Theorem 2.7 (`thm:fvl-characterization`): for a nonzero linear map of real vector
spaces, the induced algebraic free-lattice map is order continuous exactly when the
original map is injective. The collision witness proves the necessary direction. -/
theorem fvl_characterization (T : V →ₗ[ℝ] W) (hT : T ≠ 0) :
    IsOrderContinuousOp (algebraicInduced V W T).toLinearMap ↔ Function.Injective T := by
  refine ⟨?_, algebraicInduced_orderContinuous_of_injective V W T⟩
  intro h
  by_contra hn
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, T a = T b ∧ a ≠ b := by
    simpa only [Function.Injective, not_forall, exists_prop] using hn
  obtain ⟨v, hv⟩ : ∃ v, T v ≠ 0 := by
    by_contra! hz
    exact hT (LinearMap.ext hz)
  have hxy : v + (a - b) ≠ v := by simpa using sub_ne_zero.mpr hne
  have hTv : T (v + (a - b)) = T v := by simp [map_add, map_sub, hab]
  let f (n : ℕ) : AlgebraicFVL V :=
    (|algebraicDelta V (v + (a - b)) + algebraicDelta V v| -
      (n + 1 : ℝ) • |algebraicDelta V (v + (a - b)) - algebraicDelta V v|) ⊔ 0
  have hf : DecreasesToZero f := algebraic_collision_decreasesToZero V _ _ hxy
  have hc := orderContinuous_sigmaOrderContinuous _
    (fun _ h => (algebraicInduced V W T).map_nonneg h) h f hf
  have hbound : |algebraicDelta W (T v)| + |algebraicDelta W (T v)| ≤ 0 := hc.2.2 (by
    rintro _ ⟨n, rfl⟩
    intro φ
    change |φ (T v)| + |φ (T v)| ≤
      max (|φ (T (v + (a - b))) + φ (T v)| -
        (n + 1 : ℝ) * |φ (T (v + (a - b))) - φ (T v)|) 0
    simp [hTv, ← two_mul, abs_mul])
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℝ hv
  have hh := hbound φ
  change |φ (T v)| + |φ (T v)| ≤ (0 : ℝ) at hh
  norm_num [hφ] at hh

/-- The zero linear map induces the zero lattice map, which is order continuous.
Together with `fvl_characterization`, this covers every algebraic linear map, including
the zero case noted after Theorem 2.7. -/
theorem algebraic_zero_orderContinuous :
    IsOrderContinuousOp (algebraicInduced V W 0).toLinearMap := by
  have hz (f : AlgebraicFVL V) : algebraicInduced V W 0 f = 0 :=
    Subtype.ext (funext fun φ => by
      change f.1 (φ.comp 0) = 0
      simpa only [LinearMap.comp_zero] using algebraic_apply_zero V f)
  intro ι _ _ _ x a _
  change OrderConvergesTo (fun i => algebraicInduced V W 0 (x i)) (algebraicInduced V W 0 a)
  simpa only [hz] using
    (orderConvergesTo_const (ι := ι) (0 : AlgebraicFVL W))
end Algebraic

/-- Bridge between the algebraic-dual and BanLat's normed-space model of FVL. -/
theorem algebraic_normed_identification :
    ∃ U : VecLatEquiv (AlgebraicFVL E) (FVL E),
      ∀ (v : AlgebraicFVL E) (φ : FVLv.dualUnitBall E),
        U v φ = v.1 (WeakDual.toStrongDual φ.1).toLinearMap := by
  let L : VecLatHom (FVL E) (AlgebraicFVL E) := FVLv.lift (algebraicDelta E)
  have heval (v : FVL E) (φ : FVLv.dualUnitBall E) :
      (L v).1 (WeakDual.toStrongDual φ.1).toLinearMap = v φ := by
    let evA : VecLatHom (AlgebraicFVL E) ℝ :=
      { toFun := fun f => f.1 (WeakDual.toStrongDual φ.1).toLinearMap
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        map_sup' := fun _ _ => rfl
        map_inf' := fun _ _ => rfl }
    let evF : VecLatHom (FVL E) ℝ :=
      { toFun := fun f => f φ
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        map_sup' := fun _ _ => rfl
        map_inf' := fun _ _ => rfl }
    have heq : evA.comp L = evF := FVLv.hom_ext fun x => by
      change evA (FVLv.lift (algebraicDelta E) (FVLv.of x)) = φ.1 x
      rw [FVLv.lift_of]
      rfl
    exact DFunLike.congr_fun heq v
  have hinj : Function.Injective L := fun f g h => Subtype.ext (ContinuousMap.ext fun φ => by
    rw [← heval f φ, ← heval g φ, h])
  let H := (algebraicFreeSublattice E).subtype.comp L
  let C : VectorSublattice ((E →ₗ[ℝ] ℝ) → ℝ) :=
    { toSubmodule := H.toLinearMap.range
      sup_mem' := by
        rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
        exact ⟨f ⊔ g, map_sup H f g⟩ }
  have hsurj : Function.Surjective L := by
    intro v
    have hv : v.1 ∈ C := by
      apply VectorSublattice.generated_le (Y := C) _ v.2
      rintro _ ⟨x, rfl⟩
      exact ⟨FVLv.of x, congrArg Subtype.val (FVLv.lift_of (algebraicDelta E) x)⟩
    obtain ⟨f, hf⟩ := hv
    exact ⟨f, Subtype.ext hf⟩
  let U : VecLatEquiv (FVL E) (AlgebraicFVL E) :=
    { LinearEquiv.ofBijective L.toLinearMap ⟨hinj, hsurj⟩ with
      map_sup' := map_sup L
      map_inf' := map_inf L }
  refine ⟨U.symm, fun v φ => ?_⟩
  exact (heval (U.symm v) φ).symm.trans
    (congrArg (fun f : AlgebraicFVL E => f.1 (WeakDual.toStrongDual φ.1).toLinearMap)
      (U.toLinearEquiv.apply_symm_apply v))


end FBLOrderContinuousLH
