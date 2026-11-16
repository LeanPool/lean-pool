/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

public import LeanPool.MultiplicativeErgodic.GrassmannianContraction

/-!
# Strong measurability

The paper's `𝓢𝓜(Ω → 𝓑(X))` is the Borel σ-algebra of the *strong* operator topology, i.e.
`ω ↦ A(ω)x` measurable for each fixed `x` (Section 2 of `proof_met.tex`, quoting
González-Tokman–Quas Lemma A.4 for the equivalence). That is strictly weaker than measurability
into the operator-norm topology, `𝓑(X)` not being separable, so `bernstein_measurable` — which
is a statement about the norm topology — does not compose with a cocycle.

This file supplies the strong-operator versions that `Cocycle.lean` actually needs:

* `measurable_apply_of_weak` — strong measurability survives evaluation at a *measurable*
  vector, which is what makes `𝓛^{(n)}` strongly measurable by induction on `n`;
* `measurable_bernstein_of_weak` — `ω ↦ ρ_k(A(ω))` is measurable, both suprema being taken over
  countable dense sets;
* `bernsteinNumber_comp_le_mul_norm` — the submultiplicativity `ρ_k(S∘T) ≤ ρ_k(S)‖T‖` used to
  compare `χ_k(ω)` with `χ_k(σω)`.

Separability of `X` is used throughout and is the paper's standing hypothesis.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter TopologicalSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]


/-- **`ρ_k(S∘T) ≤ ρ_k(S)‖T‖`.** One half of the paper's `growth_ineq` promoted from subspaces
to Bernstein numbers. The image `T(V)` is again `k`-dimensional exactly when `T` is injective
on `V`, which `growth T V > 0` supplies; in the remaining case the other half of `growth_ineq`
already forces `g_{S∘T}(V) = 0`. -/
theorem bernsteinNumber_comp_le_mul_norm (S T : X →L[ℝ] X) (k : ℕ) :
    bernsteinNumber (S.comp T) k ≤ bernsteinNumber S k * ‖T‖ := by
  refine Real.sSup_le ?_ (mul_nonneg (bernsteinNumber_nonneg S k) (norm_nonneg T))
  rintro _ ⟨V, rfl⟩
  have hmin := (growth_ineq (T : X →L[ℝ] X) S (V.1 : Submodule ℝ X)).2
  rcases le_or_gt (growth T (V.1 : Submodule ℝ X)) 0 with h0 | h0
  · have h1 : growth T (V.1 : Submodule ℝ X) = 0 :=
      le_antisymm h0 (growth_nonneg _ _)
    have := le_trans hmin (min_le_right _ _)
    rw [h1, zero_mul] at this
    exact le_trans this (mul_nonneg (bernsteinNumber_nonneg S k) (norm_nonneg T))
  · -- `T` is injective on `V`, so `T(V)` is another `k`-dimensional subspace
    have : FiniteDimensional ℝ (V.1 : Submodule ℝ X) := V.2.1
    have hinj : Function.Injective (T.toLinearMap.domRestrict (V.1 : Submodule ℝ X)) :=
      injective_domRestrict_of_growth_pos h0
    set W : Submodule ℝ X := (V.1 : Submodule ℝ X).map (T.toLinearMap) with hW
    have : FiniteDimensional ℝ W := by rw [hW]; infer_instance
    have hrank : Module.finrank ℝ W = k := by
      have hrange := LinearMap.finrank_range_of_inj hinj
      rw [LinearMap.range_domRestrict] at hrange
      rw [hW]
      exact hrange.trans V.2.2
    have hle : growth S W ≤ bernsteinNumber S k :=
      le_csSup ⟨‖S‖, by rintro _ ⟨U, rfl⟩; exact growth_le_opNorm S _⟩
        ⟨⟨W, inferInstance, hrank⟩, rfl⟩
    calc growth (S.comp T) (V.1 : Submodule ℝ X)
        ≤ ‖T‖ * growth S W := le_trans hmin (min_le_left _ _)
      _ ≤ ‖T‖ * bernsteinNumber S k := by
          exact mul_le_mul_of_nonneg_left hle (norm_nonneg T)
      _ = bernsteinNumber S k * ‖T‖ := mul_comm _ _


/-- **`ρ_k(S∘T) ≤ ‖S‖ ρ_k(T)`**, the companion of `bernsteinNumber_comp_le_mul_norm` with the
norm on the *outer* factor. This is the direction that propagates degeneracy forwards: once
`ρ_k(𝓛^{(n₀)}_ω) = 0`, every later iterate has `ρ_k = 0` as well. -/
theorem bernsteinNumber_comp_le_norm_mul (S T : X →L[ℝ] X) (k : ℕ) :
    bernsteinNumber (S.comp T) k ≤ ‖S‖ * bernsteinNumber T k := by
  refine Real.sSup_le ?_ (mul_nonneg (norm_nonneg S) (bernsteinNumber_nonneg T k))
  rintro _ ⟨V, rfl⟩
  have hTle : growth T (V.1 : Submodule ℝ X) ≤ bernsteinNumber T k :=
    le_csSup ⟨‖T‖, by rintro _ ⟨U, rfl⟩; exact growth_le_opNorm T _⟩ ⟨V, rfl⟩
  have hle : growth (S.comp T) (V.1 : Submodule ℝ X) ≤ ‖S‖ * growth T (V.1 : Submodule ℝ X) := by
    rcases (Metric.sphere (0 : X) 1 ∩ ((V.1 : Submodule ℝ X) : Set X)).eq_empty_or_nonempty with
      he | hne
    · change sInf _ ≤ _
      rw [he, Set.image_empty, Real.sInf_empty]
      exact mul_nonneg (norm_nonneg S) (growth_nonneg T _)
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      have hSpos : (0 : ℝ) < ‖S‖ + 1 := by positivity
      have hlt : growth T (V.1 : Submodule ℝ X)
          < growth T (V.1 : Submodule ℝ X) + ε / (‖S‖ + 1) := by
        have : (0 : ℝ) < ε / (‖S‖ + 1) := by positivity
        linarith
      obtain ⟨_, ⟨x, hx, rfl⟩, hxlt⟩ := exists_lt_of_csInf_lt (hne.image _) hlt
      have h1 : growth (S.comp T) (V.1 : Submodule ℝ X) ≤ ‖S (T x)‖ :=
        csInf_le ⟨0, by rintro _ ⟨z, -, rfl⟩; exact norm_nonneg _⟩ ⟨x, hx, rfl⟩
      have h2 : ‖S (T x)‖ ≤ ‖S‖ * ‖T x‖ := S.le_opNorm _
      have h3 : ‖S‖ * ‖T x‖
          ≤ ‖S‖ * (growth T (V.1 : Submodule ℝ X) + ε / (‖S‖ + 1)) :=
        mul_le_mul_of_nonneg_left hxlt.le (norm_nonneg S)
      have h4 : ‖S‖ * (ε / (‖S‖ + 1)) ≤ ε := by
        rw [mul_div_assoc'] at *
        rw [div_le_iff₀ hSpos]
        nlinarith [norm_nonneg S, hε.le]
      nlinarith [h1, h2, h3, h4]
  refine hle.trans (mul_le_mul_of_nonneg_left hTle (norm_nonneg S))

/-- `g_T(V)` is already determined by a dense subset of the unit sphere of `V`: `x ↦ ‖Tx‖` is
Lipschitz, so the infimum cannot drop on passing to the closure. Phrased as a countable `⨅`
because that is the form measurability arguments need. -/
theorem growth_eq_ciInf (T : X →L[ℝ] X) (V : Submodule ℝ X) {S : Set X} [Nonempty S]
    (hSsub : S ⊆ Metric.sphere (0 : X) 1 ∩ (V : Set X))
    (hSdense : Metric.sphere (0 : X) 1 ∩ (V : Set X) ⊆ closure S) :
    growth T V = ⨅ x : S, ‖T (x : X)‖ := by
  have hbdd : BddBelow (Set.range fun x : S => ‖T (x : X)‖) := ⟨0, by
    rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
  have hbdd' : BddBelow ((fun x : X => ‖T x‖) '' (Metric.sphere (0 : X) 1 ∩ (V : Set X))) :=
    ⟨0, by rintro _ ⟨x, -, rfl⟩; exact norm_nonneg _⟩
  refine le_antisymm (le_ciInf fun x => ?_) ?_
  · exact csInf_le hbdd' ⟨(x : X), hSsub x.2, rfl⟩
  · obtain ⟨x₀⟩ := ‹Nonempty S›
    refine le_csInf ⟨‖T (x₀ : X)‖, ⟨(x₀ : X), hSsub x₀.2, rfl⟩⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    refine le_of_forall_pos_le_add_mul (norm_nonneg T) fun ε hε => ?_
    obtain ⟨x, hxS, hxy⟩ := Metric.mem_closure_iff.1 (hSdense hy) ε hε
    have h1 : (⨅ x : S, ‖T (x : X)‖) ≤ ‖T x‖ := ciInf_le hbdd ⟨x, hxS⟩
    have h2 : ‖T x‖ ≤ ‖T y‖ + ‖T‖ * ε := by
      have : ‖T x - T y‖ ≤ ‖T‖ * ε := by
        rw [← map_sub]
        refine le_trans (T.le_opNorm _) ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg T)
        rw [← dist_eq_norm, dist_comm]
        exact hxy.le
      have h3 : ‖T x‖ - ‖T y‖ ≤ ‖T x - T y‖ := norm_sub_norm_le _ _
      linarith
    linarith

/-- The unit sphere of a nonzero subspace of a separable space is itself separable, so `growth`
against it is a countable infimum: this is the ingredient that makes `g_{A(ω)}(V)` measurable
for a merely *strongly* measurable `A` (measurable in the strong operator topology, i.e.
`ω ↦ A(ω)x` measurable for each fixed `x`). -/
theorem measurable_growth_of_weak {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SeparableSpace X] {A : Ω → X →L[ℝ] X}
    (hA : ∀ x : X, Measurable fun ω => A ω x) (V : Submodule ℝ X)
    (hV : (Metric.sphere (0 : X) 1 ∩ (V : Set X)).Nonempty) :
    Measurable fun ω => growth (A ω) V := by
  have : SecondCountableTopology X := UniformSpace.secondCountable_of_separable X
  set K : Set X := Metric.sphere (0 : X) 1 ∩ (V : Set X) with hK
  have : Nonempty K := hV.to_subtype
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense K
  have : Countable D := hDcount.to_subtype
  have : Nonempty D := by
    obtain ⟨x, hx, -⟩ := hDdense.exists_mem_open isOpen_univ Set.univ_nonempty
    exact ⟨⟨_, hx⟩⟩
  set S : Set X := Subtype.val '' D with hS
  have : Nonempty S := by
    obtain ⟨d⟩ := ‹Nonempty D›
    exact ⟨⟨((d : K) : X), ⟨d, d.2, rfl⟩⟩⟩
  have : Countable S := by
    rw [hS]; exact (hDcount.image _).to_subtype
  have hSsub : S ⊆ K := by rintro _ ⟨d, -, rfl⟩; exact (d : K).2
  have hSdense : K ⊆ closure S := by
    intro y hy
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨d, hdD, hd⟩ := Metric.mem_closure_iff.1 (hDdense (⟨y, hy⟩ : K)) ε hε
    exact ⟨((d : K) : X), ⟨d, hdD, rfl⟩, hd⟩
  have heq : ∀ ω, growth (A ω) V = ⨅ x : S, ‖A ω (x : X)‖ :=
    fun ω => growth_eq_ciInf (A ω) V hSsub hSdense
  simp_rw [heq]
  exact Measurable.iInf fun x => (hA (x : X)).norm


/-- **Strong measurability is closed under evaluation at a measurable vector.**

The paper's `𝓢𝓜(Ω → 𝓑(X))` is the Borel σ-algebra of the *strong* operator topology, i.e.
`ω ↦ A(ω)x` measurable for each fixed `x` (its Lemma after `\ref{GXpush}`, citing
Gonz\'alez-Tokman--Quas Lemma A.4). That definition is only usable once one knows it survives
feeding in a varying vector, which is what makes `𝓛^{(n)}` strongly measurable by induction on
`n`. Separability of `X` is exactly what is needed: `v` is then a pointwise limit of
countably-valued measurable functions, on each of which the claim is a countable case split, and
`A(ω)` is continuous so the limit passes through. -/
theorem measurable_apply_of_weak {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [BorelSpace X] [SeparableSpace X] {A : Ω → X →L[ℝ] X}
    (hA : ∀ x : X, Measurable fun ω => A ω x) {v : Ω → X} (hv : Measurable v) :
    Measurable fun ω => A ω (v ω) := by
  have : SecondCountableTopology X := UniformSpace.secondCountable_of_separable X
  have hsm : StronglyMeasurable v := hv.stronglyMeasurable
  have hmeas : ∀ m : ℕ, Measurable fun ω => A ω (hsm.approx m ω) :=
    fun m => (hsm.approx m).measurable_bind (fun y ω => A ω y) hA
  refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun ω => ?_)
  exact ((A ω).continuous.tendsto (v ω)).comp (hsm.tendsto_approx ω)

/-- A `k`-dimensional subspace with `k ≥ 1` has a nonempty unit sphere. -/
theorem sphere_inter_nonempty_of_finrank {k : ℕ} [NeZero k] (V : GrassmannianFin X k) :
    (Metric.sphere (0 : X) 1 ∩ ((V.1 : Submodule ℝ X) : Set X)).Nonempty := by
  have hne : (V.1 : Submodule ℝ X) ≠ ⊥ := by
    intro hbot
    have : Module.finrank ℝ (V.1 : Submodule ℝ X) = 0 := by rw [hbot]; simp
    exact NeZero.ne k (by rw [← V.2.2, this])
  obtain ⟨x, hxV, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨‖x‖⁻¹ • x,
    mem_sphere_zero_iff_norm.2
      (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]),
    (V.1 : Submodule ℝ X).smul_mem _ hxV⟩

/-- **`ρ_k` of a strongly measurable operator family is measurable.** The strong-operator-topology
counterpart of `bernstein_measurable`: it is `ω ↦ A(ω)x` that is assumed measurable, not
`ω ↦ A(ω)` in operator norm (which is genuinely stronger, `𝓑(X)` not being separable). Both
suprema in `ρ_k = sup_V inf_{x ∈ 𝕊_V} ‖A(ω)x‖` are taken over countable dense sets, so the whole
expression is a countable lattice operation applied to the coordinate functions. -/
theorem measurable_bernstein_of_weak {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SeparableSpace X] (k : ℕ) [NeZero k] {A : Ω → X →L[ℝ] X}
    (hA : ∀ x : X, Measurable fun ω => A ω x) :
    Measurable fun ω => bernsteinNumber (A ω) k := by
  rcases isEmpty_or_nonempty (GrassmannianFin X k) with hE | hNE
  · have : ∀ ω, bernsteinNumber (A ω) k = 0 := by
      intro ω
      change sSup _ = 0
      rw [Set.range_eq_empty, Real.sSup_empty]
    simp_rw [this]
    exact measurable_const
  · have := grassmannianFin_separable (X := X) k
    obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense (GrassmannianFin X k)
    have : Countable D := hDcount.to_subtype
    have : Nonempty D := by
      obtain ⟨V, hV, -⟩ := hDdense.exists_mem_open isOpen_univ Set.univ_nonempty
      exact ⟨⟨V, hV⟩⟩
    have heq : ∀ ω, bernsteinNumber (A ω) k =
        ⨆ V : D, growth (A ω) ((V : GrassmannianFin X k).1 : Submodule ℝ X) :=
      fun ω => bernsteinNumber_eq_ciSup_dense k (A ω) hDdense
    simp_rw [heq]
    exact Measurable.iSup fun V =>
      measurable_growth_of_weak hA _ (sphere_inter_nonempty_of_finrank _)

end MultiplicativeErgodic
