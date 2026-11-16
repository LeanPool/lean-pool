/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Cocycle
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.MeasurableSpace.Card
public import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Appendix: equivalence of growth statistics, and a measurability counterexample

Corresponds to the Appendix of `proof_met.tex`.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter TopologicalSpace Module

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The Gelfand numbers `s_k(T) = inf_{V ∈ 𝒢^{k-1}X} ‖T|_V‖`. -/
noncomputable def gelfand (T : X →L[ℝ] X) (k : ℕ) : ℝ :=
  sInf (Set.range fun V : GrassmannianCofin X (k - 1) =>
    ‖T.comp (V.1.1 : Submodule ℝ X).subtypeL‖)

/-- The "compactness seminorm" `‖T‖_c`, the distance from `T` to the compact operators. -/
noncomputable def compactSeminorm (T : X →L[ℝ] X) : ℝ :=
  sInf ((fun K : X →L[ℝ] X => ‖T - K‖) '' {K | IsCompactOperator K})

/-- If `X` carries a finite-dimensional subspace of dimension `m`, then `𝒢^m X` is nonempty:
a topological complement of that subspace is closed, of finite codimension `m`, and hence
itself closed-complemented. -/
theorem nonempty_grassmannianCofin {m : ℕ} (U : Submodule ℝ X) [FiniteDimensional ℝ U]
    (hU : Module.finrank ℝ U = m) : Nonempty (GrassmannianCofin X m) := by
  have hc : U.ClosedComplemented := Submodule.ClosedComplemented.of_finiteDimensional U
  obtain ⟨q, hqclosed, hcompl⟩ := hc.exists_isClosed_isCompl
  have e : (X ⧸ q) ≃ₗ[ℝ] U := Submodule.quotientEquivOfIsCompl q U hcompl.symm
  have : FiniteDimensional ℝ (X ⧸ q) := e.symm.finiteDimensional
  have hq : q.ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional_quotient hqclosed
  exact ⟨⟨⟨q, hq⟩, ⟨inferInstance, by rw [e.finrank_eq, hU]⟩⟩⟩

/-- A `k`-dimensional subspace meets every subspace of codimension `k-1` nontrivially,
provided `k ≥ 1`. -/
theorem exists_ne_zero_mem_inf_of_finrank_quotient {k : ℕ} (hk : 1 ≤ k)
    (V W : Submodule ℝ X) (hV : Module.finrank ℝ V = k)
    [FiniteDimensional ℝ (X ⧸ W)] (hW : Module.finrank ℝ (X ⧸ W) = k - 1) :
    ∃ x ∈ V ⊓ W, x ≠ 0 := by
  refine Submodule.exists_mem_ne_zero_of_ne_bot ?_
  intro h0
  have hker : LinearMap.ker (W.mkQ.comp V.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have hvW : (v : X) ∈ W := by
      have : W.mkQ (v : X) = 0 := hv
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    have hmem : (v : X) ∈ V ⊓ W := ⟨v.2, hvW⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  have hle := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.1 hker)
  rw [hV, hW] at hle
  omega

/-- `s_k(T) ≥ 0`: it is an infimum of operator norms. -/
theorem gelfand_nonneg (T : X →L[ℝ] X) (k : ℕ) : 0 ≤ gelfand T k := by
  unfold gelfand
  refine Real.sInf_nonneg ?_
  rintro _ ⟨W, rfl⟩
  positivity

/-- A subspace of codimension `0` is the whole space. -/
theorem GrassmannianCofin.eq_top_of_zero (V : GrassmannianCofin X 0) :
    (V.1.1 : Submodule ℝ X) = ⊤ := by
  have : FiniteDimensional ℝ (X ⧸ (V.1.1 : Submodule ℝ X)) := V.2.1
  have hsub : Subsingleton (X ⧸ (V.1.1 : Submodule ℝ X)) := Module.finrank_zero_iff.1 V.2.2
  exact Submodule.Quotient.subsingleton_iff.1 hsub

/-- Restricting to `⊤` does not change the operator norm. -/
theorem opNorm_comp_subtypeL_of_eq_top (T : X →L[ℝ] X) {W : Submodule ℝ X} (hW : W = ⊤) :
    ‖T.comp W.subtypeL‖ = ‖T‖ := by
  subst hW
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun y => ?_
    simpa using T.le_opNorm (y : X)
  · refine T.opNorm_le_bound (norm_nonneg (T.comp (⊤ : Submodule ℝ X).subtypeL)) fun x => ?_
    simpa using (T.comp (⊤ : Submodule ℝ X).subtypeL).le_opNorm ⟨x, Submodule.mem_top⟩

/-- `s_1(T) = ‖T‖`: the only subspace of codimension `0` is `X` itself. -/
theorem gelfand_one (T : X →L[ℝ] X) : gelfand T 1 = ‖T‖ := by
  have hne : Nonempty (GrassmannianCofin X 0) :=
    nonempty_grassmannianCofin (⊥ : Submodule ℝ X) (by simp)
  have hrange : (Set.range fun V : GrassmannianCofin X (1 - 1) =>
      ‖T.comp (V.1.1 : Submodule ℝ X).subtypeL‖) = {‖T‖} := by
    ext r
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨V, rfl⟩
      exact opNorm_comp_subtypeL_of_eq_top T (GrassmannianCofin.eq_top_of_zero V)
    · rintro rfl
      obtain ⟨V⟩ := hne
      exact ⟨V, opNorm_comp_subtypeL_of_eq_top T (GrassmannianCofin.eq_top_of_zero V)⟩
  change sInf _ = _
  rw [hrange, csInf_singleton]

/-- **Codimension can always be raised by one inside a given subspace**, as long as that subspace
is nonzero: a continuous functional `f` not vanishing on `W` makes `x ↦ (x mod W, f x)` a
surjection onto `(X ⧸ W) × ℝ` whose kernel `W ⊓ ker f` therefore has codimension `m + 1`.

This is what makes the Gelfand numbers antitone, which the appendix's induction uses in the
form `s_k ≤ s_{k-1}`. -/
theorem exists_grassmannianCofin_succ_le (m : ℕ) (W : GrassmannianCofin X m)
    (hne : (W.1.1 : Submodule ℝ X) ≠ ⊥) :
    ∃ W' : GrassmannianCofin X (m + 1),
      (W'.1.1 : Submodule ℝ X) ≤ (W.1.1 : Submodule ℝ X) := by
  set V : Submodule ℝ X := (W.1.1 : Submodule ℝ X) with hVdef
  have : FiniteDimensional ℝ (X ⧸ V) := W.2.1
  obtain ⟨u, huV, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨f, -, hfu⟩ := exists_dual_vector ℝ u (by rwa [ne_eq, norm_eq_zero])
  have hfu0 : f u ≠ 0 := by rw [hfu]; exact norm_ne_zero_iff.2 hu0
  set g : X →ₗ[ℝ] (X ⧸ V) × ℝ := (V.mkQ).prod (f : X →ₗ[ℝ] ℝ) with hgdef
  have hker : LinearMap.ker g = V ⊓ LinearMap.ker (f : X →ₗ[ℝ] ℝ) := by
    ext x
    constructor
    · intro hx
      have hx0 : g x = 0 := hx
      have h1 : V.mkQ x = 0 := congrArg Prod.fst hx0
      have h2 : f x = 0 := congrArg Prod.snd hx0
      exact ⟨(Submodule.Quotient.mk_eq_zero V).1 h1, h2⟩
    · rintro ⟨h1, h2⟩
      change g x = 0
      have h1' : V.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero V).2 h1
      exact Prod.ext h1' h2
  have hsurj : Function.Surjective g := by
    rintro ⟨v, t⟩
    obtain ⟨x₀, rfl⟩ := V.mkQ_surjective v
    refine ⟨x₀ + ((t - f x₀) / f u) • u, ?_⟩
    have h1 : V.mkQ (x₀ + ((t - f x₀) / f u) • u) = V.mkQ x₀ := by
      rw [map_add, map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero V).2 huV, smul_zero, add_zero]
    have h2 : f (x₀ + ((t - f x₀) / f u) • u) = t := by
      rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfu0]
      ring
    exact Prod.ext h1 h2
  let e : (X ⧸ LinearMap.ker g) ≃ₗ[ℝ] (X ⧸ V) × ℝ := g.quotKerEquivOfSurjective hsurj
  have : FiniteDimensional ℝ ((X ⧸ V) × ℝ) := inferInstance
  have hfd : FiniteDimensional ℝ (X ⧸ LinearMap.ker g) := e.symm.finiteDimensional
  have hrank : Module.finrank ℝ (X ⧸ LinearMap.ker g) = m + 1 := by
    rw [e.finrank_eq, Module.finrank_prod, W.2.2, Module.finrank_self]
  have hclosed : IsClosed ((LinearMap.ker g : Submodule ℝ X) : Set X) := by
    rw [hker]
    exact (W.1.2.isClosed).inter (isClosed_eq f.continuous continuous_const)
  have hcc : (LinearMap.ker g).ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional_quotient hclosed
  have hle : (LinearMap.ker g : Submodule ℝ X) ≤ V := by rw [hker]; exact inf_le_left
  exact ⟨⟨⟨LinearMap.ker g, hcc⟩, hfd, hrank⟩, hle⟩

/-- **Codimension can always be lowered by one.** A `1`-dimensional subspace of the (nonzero,
finite-dimensional) quotient `X ⧸ W'` pulls back to a `W ⊇ W'` of codimension one less; `W` is
closed because it contains the closed finite-codimensional `W'`.

Needed to see that `𝒢^jX` cannot be empty while `𝒢^{j+1}X` is not, which is the degenerate case
of `gelfand_succ_le`. -/
theorem exists_grassmannianCofin_of_succ (j : ℕ) (W' : GrassmannianCofin X (j + 1)) :
    Nonempty (GrassmannianCofin X j) := by
  set P : Submodule ℝ X := (W'.1.1 : Submodule ℝ X) with hP
  have hfdQ : FiniteDimensional ℝ (X ⧸ P) := W'.2.1
  have hPclosed : IsClosed ((P : Submodule ℝ X) : Set X) := W'.1.2.isClosed
  -- a line in the quotient
  have hQne : ∃ y : X ⧸ P, y ≠ 0 := by
    by_contra hcon
    rw [not_exists] at hcon
    have : Subsingleton (X ⧸ P) := ⟨fun a b => by rw [not_not.1 (hcon a), not_not.1 (hcon b)]⟩
    have := Module.finrank_zero_of_subsingleton (R := ℝ) (M := X ⧸ P)
    rw [W'.2.2] at this
    omega
  obtain ⟨y, hy⟩ := hQne
  set S : Submodule ℝ (X ⧸ P) := Submodule.span ℝ {y} with hS
  have hSrank : Module.finrank ℝ S = 1 := finrank_span_singleton hy
  set W : Submodule ℝ X := Submodule.comap P.mkQ S with hW
  have hPW : P ≤ W := by
    intro x hx
    change P.mkQ x ∈ S
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).2 hx]
    exact Submodule.zero_mem S
  have hWclosed : IsClosed ((W : Submodule ℝ X) : Set X) :=
    Submodule.isClosed_mono_of_finiteDimensional_quotient hPclosed hPW
  have hmap : Submodule.map P.mkQ W = S := by
    rw [hW, Submodule.map_comap_eq_of_surjective P.mkQ_surjective]
  have e : ((X ⧸ P) ⧸ S) ≃ₗ[ℝ] X ⧸ W := by
    have := Submodule.quotientQuotientEquivQuotient P W hPW
    rwa [hmap] at this
  have : FiniteDimensional ℝ ((X ⧸ P) ⧸ S) := inferInstance
  have hfdW : FiniteDimensional ℝ (X ⧸ W) := e.finiteDimensional
  have hrank : Module.finrank ℝ (X ⧸ W) = j := by
    have hsum := Submodule.finrank_quotient_add_finrank S
    rw [e.finrank_eq, hSrank, W'.2.2] at hsum
    omega
  exact ⟨⟨⟨W, Submodule.ClosedComplemented.of_finiteDimensional_quotient hWclosed⟩, hfdW, hrank⟩⟩

/-- `s_{m+1}` with its index already reduced, so that the `GrassmannianCofin` index is a literal
variable. Instance search works only up to reducible transparency, and will not see through the
`k - 1` in the definition of `gelfand`. -/
theorem gelfand_succ (T : X →L[ℝ] X) (m : ℕ) :
    gelfand T (m + 1) =
      sInf (Set.range fun V : GrassmannianCofin X m =>
        ‖T.comp (V.1.1 : Submodule ℝ X).subtypeL‖) := rfl

/-- Restricting further can only shrink the operator norm. -/
theorem opNorm_comp_subtypeL_mono (T : X →L[ℝ] X) {W' W : Submodule ℝ X} (h : W' ≤ W) :
    ‖T.comp W'.subtypeL‖ ≤ ‖T.comp W.subtypeL‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (norm_nonneg (T.comp W.subtypeL)) fun y => ?_
  have := (T.comp W.subtypeL).le_opNorm ⟨(y : X), h y.2⟩
  simpa using this

/-- **The Gelfand numbers are antitone**: `s_{k+1} ≤ s_k`. Every subspace of codimension `k - 1`
either is `⊥` — in which case `X` is `(k-1)`-dimensional, so nothing has codimension `k` and
`s_{k+1}` is the junk value `sInf ∅ = 0` — or contains one of codimension `k`, by
`exists_grassmannianCofin_succ_le`. -/
theorem gelfand_succ_le (T : X →L[ℝ] X) (k : ℕ) : gelfand T (k + 1) ≤ gelfand T k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact le_of_eq rfl
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [gelfand_succ T (j + 1), gelfand_succ T j]
    rcases isEmpty_or_nonempty (GrassmannianCofin X (j + 1)) with hE | hne
    · rw [Set.range_eq_empty, Real.sInf_empty]
      refine Real.sInf_nonneg ?_
      rintro _ ⟨W, rfl⟩
      positivity
    · have := hne
      have := exists_grassmannianCofin_of_succ j
        (Classical.arbitrary (GrassmannianCofin X (j + 1)))
      refine le_csInf (Set.range_nonempty _) ?_
      rintro _ ⟨W, rfl⟩
      change sInf _ ≤ ‖T.comp (W.1.1 : Submodule ℝ X).subtypeL‖
      by_cases hbot : (W.1.1 : Submodule ℝ X) = ⊥
      · exfalso
        obtain ⟨V⟩ := hne
        have : FiniteDimensional ℝ (X ⧸ (V.1.1 : Submodule ℝ X)) := V.2.1
        have e : (X ⧸ (⊥ : Submodule ℝ X)) ≃ₗ[ℝ] X := Submodule.quotEquivOfEqBot ⊥ rfl
        have : FiniteDimensional ℝ (X ⧸ (⊥ : Submodule ℝ X)) := hbot ▸ W.2.1
        have : FiniteDimensional ℝ X := e.finiteDimensional
        have hXrank : Module.finrank ℝ X = j := by
          have hw := W.2.2
          rw [hbot] at hw
          rw [← e.finrank_eq, hw]
        have hle := Submodule.finrank_quotient_le (V.1.1 : Submodule ℝ X)
        rw [V.2.2, hXrank] at hle
        omega
      · obtain ⟨W', hW'⟩ := exists_grassmannianCofin_succ_le j W hbot
        refine le_trans ?_ (opNorm_comp_subtypeL_mono T hW')
        exact csInf_le ⟨0, by rintro _ ⟨U, rfl⟩; positivity⟩ ⟨W', rfl⟩

/-- `s` is antitone in the index. -/
theorem gelfand_antitone (T : X →L[ℝ] X) {j k : ℕ} (h : j ≤ k) : gelfand T k ≤ gelfand T j := by
  induction k with
  | zero =>
      have : j = 0 := by omega
      subst this
      exact le_rfl
  | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with hj | hj
      · exact le_trans (gelfand_succ_le T k) (ih (by omega))
      · have : j = k + 1 := by omega
        subst this
        exact le_rfl

/-- A unit vector nearly attaining the operator norm. -/
theorem exists_unit_norm_ge_sub {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [Nontrivial Y] (f : Y →L[ℝ] Z) {ε : ℝ}
    (hε : 0 < ε) : ∃ y : Y, ‖y‖ = 1 ∧ ‖f‖ - ε ≤ ‖f y‖ := by
  obtain ⟨y₀, hy₀⟩ := exists_ne (0 : Y)
  have hnorm : ‖‖y₀‖⁻¹ • y₀‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hy₀)]
  rcases le_or_gt (‖f‖ - ε) 0 with hle | hpos
  · exact ⟨_, hnorm, hle.trans (norm_nonneg _)⟩
  · by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    have hb : ‖f‖ ≤ ‖f‖ - ε := by
      refine f.opNorm_le_bound hpos.le fun y => ?_
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      · have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy
        have hy1 : ‖‖y‖⁻¹ • y‖ = 1 := by
          rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hy)]
        have hlt := (hcon _ hy1).le
        rw [map_smul, norm_smul, norm_inv, norm_norm] at hlt
        have := mul_le_mul_of_nonneg_left hlt hypos.le
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hypos), one_mul] at this
        linarith [this]
    linarith

/-- The preimage of a closed finite-codimensional subspace is again closed of finite
codimension, and the codimension does not go up: `X ⧸ T⁻¹V` embeds in `X ⧸ V`. -/
theorem exists_grassmannianCofin_comap (T : X →L[ℝ] X) {V : Submodule ℝ X}
    (hV : IsClosed (V : Set X)) [FiniteDimensional ℝ (X ⧸ V)] :
    ∃ (j : ℕ) (S : GrassmannianCofin X j), j ≤ Module.finrank ℝ (X ⧸ V) ∧
      (S.1.1 : Submodule ℝ X) = Submodule.comap (T : X →ₗ[ℝ] X) V := by
  set g : X →ₗ[ℝ] (X ⧸ V) := V.mkQ.comp (T : X →ₗ[ℝ] X) with hg
  have hker : LinearMap.ker g = Submodule.comap (T : X →ₗ[ℝ] X) V := by
    ext x
    constructor
    · intro hx
      have : V.mkQ (T x) = 0 := hx
      exact (Submodule.Quotient.mk_eq_zero V).1 this
    · intro hx
      change V.mkQ (T x) = 0
      exact (Submodule.Quotient.mk_eq_zero V).2 hx
  let e : (X ⧸ LinearMap.ker g) ≃ₗ[ℝ] LinearMap.range g := g.quotKerEquivRange
  have hfdr : FiniteDimensional ℝ (LinearMap.range g) := inferInstance
  have hfd : FiniteDimensional ℝ (X ⧸ LinearMap.ker g) := e.symm.finiteDimensional
  have hle : Module.finrank ℝ (X ⧸ LinearMap.ker g) ≤ Module.finrank ℝ (X ⧸ V) := by
    rw [e.finrank_eq]
    exact Submodule.finrank_le _
  have hclosed : IsClosed ((LinearMap.ker g : Submodule ℝ X) : Set X) := by
    rw [hker]
    exact hV.preimage T.continuous
  have hcc : (LinearMap.ker g).ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional_quotient hclosed
  exact ⟨Module.finrank ℝ (X ⧸ LinearMap.ker g),
    ⟨⟨LinearMap.ker g, hcc⟩, hfd, rfl⟩, hle, hker⟩

/-- **Lemma.** `ρ_k ≤ s_k` (`proof_met.tex` l.1065). Given `V ∈ 𝒢_kX` nearly attaining `ρ_k`,
every `W` of codimension `k-1` meets `V` in a nonzero vector, which may be scaled to the unit
sphere; then `g_T(V) ≤ ‖Tu‖ ≤ ‖T|_W‖`. Taking the infimum over `W` gives the claim.

The degenerate cases are the junk values: `𝒢_kX` empty makes `ρ_k = sSup ∅ = 0`, and `k = 0`
makes `V = ⊥` with an empty unit sphere, so `growth T ⊥ = sInf ∅ = 0`; both are `≤ s_k`, which is
a `sInf` of norms and so nonnegative. -/
theorem bernstein_le_gelfand (T : X →L[ℝ] X) (k : ℕ) : bernsteinNumber T k ≤ gelfand T k := by
  have hgel : 0 ≤ gelfand T k := by
    unfold gelfand
    refine Real.sInf_nonneg ?_
    rintro _ ⟨W, rfl⟩
    positivity
  rcases isEmpty_or_nonempty (GrassmannianFin X k) with hE | hne
  · change sSup _ ≤ _
    rw [Set.range_eq_empty, Real.sSup_empty]
    exact hgel
  · refine Real.sSup_le ?_ hgel
    rintro _ ⟨V, rfl⟩
    dsimp only
    have hVfd : FiniteDimensional ℝ (V.1 : Submodule ℝ X) := V.2.1
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · -- `k = 0`: `V = ⊥`, so `growth T V = 0 ≤ gelfand T 0`.
      have hbot : (V.1 : Submodule ℝ X) = ⊥ := Submodule.finrank_eq_zero.1 V.2.2
      have : growth T (V.1 : Submodule ℝ X) = 0 := by
        refine growth_eq_zero_of_forall_eq_zero ?_
        intro x hx
        rw [hbot, Submodule.mem_bot] at hx
        simp [hx]
      rw [this]
      exact hgel
    · -- `k ≥ 1`: build a codimension-`(k-1)` subspace, then use dimension counting.
      obtain ⟨f, hf⟩ :=
        exists_linearIndependent_of_le_finrank (R := ℝ) (M := (V.1 : Submodule ℝ X))
          (n := k - 1) (by rw [V.2.2]; omega)
      have hg : LinearIndependent ℝ (fun i => ((f i : X))) :=
        hf.map' (V.1 : Submodule ℝ X).subtype (Submodule.ker_subtype _)
      set U : Submodule ℝ X := Submodule.span ℝ (Set.range fun i => ((f i : X))) with hUdef
      have : FiniteDimensional ℝ U :=
        FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
      have hUrank : Module.finrank ℝ U = k - 1 := by
        rw [hUdef, finrank_span_eq_card hg, Fintype.card_fin]
      have := nonempty_grassmannianCofin U hUrank
      unfold gelfand
      refine le_csInf (Set.range_nonempty _) ?_
      rintro _ ⟨W, rfl⟩
      dsimp only
      have : FiniteDimensional ℝ (X ⧸ (W.1.1 : Submodule ℝ X)) := W.2.1
      obtain ⟨x, hxmem, hx0⟩ :=
        exists_ne_zero_mem_inf_of_finrank_quotient hk (V.1 : Submodule ℝ X)
          (W.1.1 : Submodule ℝ X) V.2.2 W.2.2
      obtain ⟨hxV, hxW⟩ := hxmem
      set u : X := ‖x‖⁻¹ • x with hudef
      have hunorm : ‖u‖ = 1 := by
        rw [hudef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]
      have huV : u ∈ (V.1 : Submodule ℝ X) := Submodule.smul_mem _ _ hxV
      have huW : u ∈ (W.1.1 : Submodule ℝ X) := Submodule.smul_mem _ _ hxW
      have hgrowth : growth T (V.1 : Submodule ℝ X) ≤ ‖T u‖ :=
        csInf_le ⟨0, by rintro _ ⟨z, -, rfl⟩; exact norm_nonneg _⟩
          ⟨u, ⟨mem_sphere_zero_iff_norm.2 hunorm, huV⟩, rfl⟩
      refine hgrowth.trans ?_
      have hop := (T.comp (W.1.1 : Submodule ℝ X).subtypeL).le_opNorm ⟨u, huW⟩
      have hnu : ‖(⟨u, huW⟩ : (W.1.1 : Submodule ℝ X))‖ = 1 := hunorm
      rw [hnu, mul_one] at hop
      simpa using hop

/-- The inductive step of the appendix's `s_k ≤ c_k^{-1} ρ_k`, in its `ε`-form.

Given a `k`-dimensional `U` nearly attaining `ρ_k` and a unit `x` with `Tx` in a complement of
`T(U)` nearly attaining `s_{k+1}`, the `(k+1)`-dimensional `W = U ⊕ ⟨x⟩` has
`g_T(W) ≥ min(g_T(U), ‖Tx‖)/(2(k+1))`: the projection `Π` onto `T(U)` separates the two
components of `Ta`, and `‖Π‖ ≤ k` by Auerbach (`exists_proj_norm_le`) rather than
`√k` by Kadec--Snobar. -/
theorem bernstein_succ_ge_of_eps (T : X →L[ℝ] X) {k : ℕ} (hk : 1 ≤ k)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hεs : ε < gelfand T (k + 1))
    (hρk : 0 < bernsteinNumber T k) :
    min ((1 - ε) * bernsteinNumber T k) (gelfand T (k + 1) - ε)
      ≤ 2 * ((k : ℝ) + 1) * bernsteinNumber T (k + 1) := by
  classical
  set s : ℝ := gelfand T (k + 1) with hs
  -- (1) a near-optimal `U ∈ 𝒢_kX`
  have hne : Nonempty (GrassmannianFin X k) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have hz : bernsteinNumber T k = 0 := by
      change sSup _ = 0
      rw [Set.range_eq_empty, Real.sSup_empty]
    rw [hz] at hρk
    exact lt_irrefl 0 hρk
  have hlt : (1 - ε) * bernsteinNumber T k < bernsteinNumber T k := by
    nlinarith [mul_pos hε hρk]
  obtain ⟨_, ⟨U, rfl⟩, hU⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hlt
  have hUpos : 0 < growth T (U.1 : Submodule ℝ X) :=
    lt_of_le_of_lt (mul_nonneg (by linarith) hρk.le) hU
  have hUfd : FiniteDimensional ℝ (U.1 : Submodule ℝ X) := U.2.1
  -- (2) the image `R = T(U)` is again `k`-dimensional
  have hinj : Function.Injective (T.toLinearMap.domRestrict (U.1 : Submodule ℝ X)) :=
    injective_domRestrict_of_growth_pos hUpos
  set R : Submodule ℝ X := (U.1 : Submodule ℝ X).map T.toLinearMap with hR
  have hRfd : FiniteDimensional ℝ R := by rw [hR]; infer_instance
  have hRrank : Module.finrank ℝ R = k := by
    have hrange := LinearMap.finrank_range_of_inj hinj
    rw [LinearMap.range_domRestrict] at hrange
    rw [hR]; exact hrange.trans U.2.2
  -- (3) an Auerbach projection onto `R`
  obtain ⟨P, hP1, hP2, hPnorm⟩ := exists_proj_norm_le R hRrank
  set V : Submodule ℝ X := LinearMap.ker (P : X →ₗ[ℝ] X) with hV
  have hVclosed : IsClosed ((V : Submodule ℝ X) : Set X) := by
    have : ((V : Submodule ℝ X) : Set X) = P ⁻¹' {0} := rfl
    rw [this]
    exact isClosed_singleton.preimage P.continuous
  have hPrange : LinearMap.range (P : X →ₗ[ℝ] X) = R :=
    le_antisymm (by rintro _ ⟨x, rfl⟩; exact hP1 x) fun w hw => ⟨w, hP2 w hw⟩
  have hRangeFd : FiniteDimensional ℝ (LinearMap.range (P : X →ₗ[ℝ] X)) := by
    rw [hPrange]; exact hRfd
  have hQfd : FiniteDimensional ℝ (X ⧸ V) :=
    (LinearMap.quotKerEquivRange (P : X →ₗ[ℝ] X)).symm.finiteDimensional
  have hQrank : Module.finrank ℝ (X ⧸ V) = k := by
    rw [(LinearMap.quotKerEquivRange (P : X →ₗ[ℝ] X)).finrank_eq]
    have : LinearMap.range (P : X →ₗ[ℝ] X) = R := hPrange
    rw [this, hRrank]
  -- (4) `T⁻¹V` has codimension at most `k`, so it sees `s_{k+1}`
  obtain ⟨j, S, hjk, hSeq⟩ := exists_grassmannianCofin_comap T hVclosed
  rw [hQrank] at hjk
  have hsS : s ≤ ‖T.comp (S.1.1 : Submodule ℝ X).subtypeL‖ := by
    refine le_trans (gelfand_antitone T (by omega : j + 1 ≤ k + 1)) ?_
    rw [gelfand_succ T j]
    exact csInf_le ⟨0, by rintro _ ⟨W, rfl⟩; positivity⟩ ⟨S, rfl⟩
  -- (5) a unit vector `x ∈ T⁻¹V` with `‖Tx‖` near `s`
  have hSnt : Nontrivial (S.1.1 : Submodule ℝ X) := by
    rcases subsingleton_or_nontrivial (S.1.1 : Submodule ℝ X) with hsub | h
    · exfalso
      have : ‖T.comp (S.1.1 : Submodule ℝ X).subtypeL‖ = 0 := by
        refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ le_rfl fun y => ?_)
          (norm_nonneg (T.comp (S.1.1 : Submodule ℝ X).subtypeL))
        rw [Subsingleton.elim y 0]
        simp
      rw [this] at hsS
      linarith
    · exact h
  obtain ⟨y, hy1, hy2⟩ := exists_unit_norm_ge_sub (T.comp (S.1.1 : Submodule ℝ X).subtypeL) hε
  set x : X := (y : X) with hx
  have hxnorm : ‖x‖ = 1 := hy1
  have hTx : s - ε ≤ ‖T x‖ := by
    refine le_trans (by linarith) hy2
  have hTxV : T x ∈ V := by
    have : x ∈ Submodule.comap (T : X →ₗ[ℝ] X) V := by rw [← hSeq]; exact y.2
    exact this
  have hTxpos : 0 < ‖T x‖ := lt_of_lt_of_le (by linarith) hTx
  -- (6) `x ∉ U`, so `W = U ⊕ ⟨x⟩` is `(k+1)`-dimensional
  have hxU : x ∉ (U.1 : Submodule ℝ X) := by
    intro hmem
    have hTxR : T x ∈ R := ⟨x, hmem, rfl⟩
    have h1 : P (T x) = T x := hP2 _ hTxR
    have h2 : P (T x) = 0 := hTxV
    rw [h1] at h2
    rw [h2, norm_zero] at hTxpos
    exact lt_irrefl 0 hTxpos
  set W : Submodule ℝ X := (U.1 : Submodule ℝ X) ⊔ Submodule.span ℝ {x} with hW
  have hlinefd : FiniteDimensional ℝ (Submodule.span ℝ {x} : Submodule ℝ X) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_singleton _)
  have hWfd : FiniteDimensional ℝ W := by rw [hW]; infer_instance
  have hinf : (U.1 : Submodule ℝ X) ⊓ Submodule.span ℝ {x} = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzU, hzs⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hzs
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · exact absurd ((U.1 : Submodule ℝ X).smul_mem c⁻¹ hzU) (by
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul])
  have hWrank : Module.finrank ℝ W = k + 1 := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      (U.1 : Submodule ℝ X) (Submodule.span ℝ {x})
    rw [hinf, finrank_bot, U.2.2,
      finrank_span_singleton (by rw [← norm_ne_zero_iff, hxnorm]; norm_num)] at hsum
    rw [hW]
    omega
  -- (7) the pointwise estimate on the unit sphere of `W`
  set M : ℝ := min (growth T (U.1 : Submodule ℝ X)) ‖T x‖ with hM
  have hMnonneg : 0 ≤ M := le_min hUpos.le (norm_nonneg _)
  have hkey : ∀ a ∈ Metric.sphere (0 : X) 1 ∩ (W : Set X), M ≤ 2 * ((k : ℝ) + 1) * ‖T a‖ := by
    rintro a ⟨ha1, haW⟩
    have hanorm : ‖a‖ = 1 := mem_sphere_zero_iff_norm.1 ha1
    obtain ⟨b, hbU, z, hz, rfl⟩ := Submodule.mem_sup.1 haW
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have htri : (1 : ℝ) ≤ ‖b‖ + |c| := by
      have := norm_add_le b (c • x)
      rw [hanorm] at this
      rwa [norm_smul, Real.norm_eq_abs, hxnorm, mul_one] at this
    have hTa : T (b + c • x) = T b + c • T x := by rw [map_add, map_smul]
    have hPTa : P (T (b + c • x)) = T b := by
      rw [hTa, map_add, map_smul, (show P (T x) = 0 from hTxV), smul_zero, add_zero]
      exact hP2 _ ⟨b, hbU, rfl⟩
    have hb1 : ‖T b‖ ≤ (k : ℝ) * ‖T (b + c • x)‖ := by
      rw [← hPTa]
      refine le_trans (P.le_opNorm _) ?_
      exact mul_le_mul_of_nonneg_right hPnorm (norm_nonneg _)
    have hb2 : |c| * ‖T x‖ ≤ ((k : ℝ) + 1) * ‖T (b + c • x)‖ := by
      have hcx : ‖c • T x‖ = |c| * ‖T x‖ := by rw [norm_smul, Real.norm_eq_abs]
      have : c • T x = T (b + c • x) - T b := by rw [hTa]; abel
      rw [← hcx, this]
      calc ‖T (b + c • x) - T b‖ ≤ ‖T (b + c • x)‖ + ‖T b‖ := norm_sub_le _ _
        _ ≤ ‖T (b + c • x)‖ + (k : ℝ) * ‖T (b + c • x)‖ := by linarith
        _ = ((k : ℝ) + 1) * ‖T (b + c • x)‖ := by ring
    have hgb : growth T (U.1 : Submodule ℝ X) * ‖b‖ ≤ ‖T b‖ := growth_mul_norm_le T hbU
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hMb : M * ‖b‖ ≤ ((k : ℝ) + 1) * ‖T (b + c • x)‖ := by
      have : M * ‖b‖ ≤ growth T (U.1 : Submodule ℝ X) * ‖b‖ :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
      nlinarith [norm_nonneg (T (b + c • x))]
    have hMc : M * |c| ≤ ((k : ℝ) + 1) * ‖T (b + c • x)‖ := by
      have : M * |c| ≤ ‖T x‖ * |c| :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _)
      nlinarith
    nlinarith [hMnonneg, htri]
  have hkpos : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
  have hne' : (Metric.sphere (0 : X) 1 ∩ (W : Set X)).Nonempty := by
    refine ⟨x, mem_sphere_zero_iff_norm.2 hxnorm, ?_⟩
    exact (le_sup_right : Submodule.span ℝ {x} ≤ W) (Submodule.mem_span_singleton_self x)
  have hgW : M / (2 * ((k : ℝ) + 1)) ≤ growth T W := by
    unfold growth
    refine le_csInf (hne'.image _) ?_
    rintro _ ⟨a, ha, rfl⟩
    change M / (2 * ((k : ℝ) + 1)) ≤ ‖T a‖
    rw [div_le_iff₀ hkpos]
    have := hkey a ha
    linarith
  -- (8) conclude
  have hρ : growth T W ≤ bernsteinNumber T (k + 1) :=
    le_csSup ⟨‖T‖, by rintro _ ⟨V', rfl⟩; exact growth_le_opNorm T _⟩
      ⟨⟨W, hWfd, hWrank⟩, rfl⟩
  have hfinal : M ≤ 2 * ((k : ℝ) + 1) * bernsteinNumber T (k + 1) := by
    have h1 : M / (2 * ((k : ℝ) + 1)) ≤ bernsteinNumber T (k + 1) := le_trans hgW hρ
    rw [div_le_iff₀ hkpos] at h1
    calc M ≤ bernsteinNumber T (k + 1) * (2 * ((k : ℝ) + 1)) := h1
      _ = 2 * ((k : ℝ) + 1) * bernsteinNumber T (k + 1) := by ring
  exact le_trans (min_le_min hU.le hTx) hfinal

/-- **Lemma.** `s_k ≤ 4^{k-1} (k-1)! ρ_k` (`proof_met.tex`, appendix), for `k ≥ 1`.

**Two departures from the paper's statement, both forced.**

1. *`k ≥ 1` is needed.* The paper says "for all `k`", indexing from `1`. Read at `k = 0` the
   claim is false: the only subspace of codimension `0` is `X`, so `s_0 = ‖T‖`, while
   `ρ_0 = 0` (`bernsteinNumber_zero`) — the inequality would say `‖T‖ ≤ 0`.

2. *The constant is `(k-1)!`, not `((k-1)!)^{1/2}`.* The paper's induction chooses a projection
   onto `TU ∈ 𝒢_{k-1}X` of norm at most `√(k-1) + ε`, which is the Kadec--Snobar theorem;
   Mathlib does not have it, and it is a substantial theorem in its own right (it goes through
   John's ellipsoid). `exists_proj_norm_le` gives a projection of norm at most `k-1` from an
   Auerbach basis instead, unconditionally, which replaces the recursion
   `c_k = c_{k-1}/(4√(k-1))` by `c_k = c_{k-1}/(4(k-1))`. Nothing else in the argument changes.
   The paper itself remarks that a sharper bound is in Pietsch's work on `s`-numbers
   (`pietsch1974`), so the exact constant is not the point, and the only downstream consumer
   (`nu_eq_compactnessIndex`) takes `(1/n) log` of it, where any constant depending on `k`
   alone vanishes.

The estimate itself is `bernstein_succ_ge_of_eps`; what is left here is the induction and the
`ε → 0` limit. -/
theorem gelfand_le_bernstein (T : X →L[ℝ] X) {k : ℕ} (hk : 1 ≤ k) :
    gelfand T k ≤ 4 ^ (k - 1) * (Nat.factorial (k - 1) : ℝ) * bernsteinNumber T k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [show (1 : ℕ) - 1 = 0 from rfl, pow_zero, Nat.factorial_zero, Nat.cast_one,
        gelfand_one, bernsteinNumber_one]
      norm_num
    · have ih' := ih hk1
      set Ck : ℝ := 4 ^ (k - 1) * (Nat.factorial (k - 1) : ℝ) with hCk
      have hCkge : (1 : ℝ) ≤ Ck := by
        rw [hCk]
        have h1 : (1 : ℝ) ≤ 4 ^ (k - 1) := one_le_pow₀ (by norm_num)
        have h2 : (1 : ℝ) ≤ (Nat.factorial (k - 1) : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
        nlinarith
      have hCkpos : (0 : ℝ) < Ck := by linarith
      set Ck1 : ℝ := 4 ^ (k + 1 - 1) * (Nat.factorial (k + 1 - 1) : ℝ) with hCk1
      have hCk1eq : Ck1 = 4 * (k : ℝ) * Ck := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [hCk1, hCk]
        simp only [Nat.add_sub_cancel]
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hratio : 2 * ((k : ℝ) + 1) * Ck ≤ Ck1 := by
        have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        rw [hCk1eq]
        nlinarith
      have hρnn : 0 ≤ bernsteinNumber T (k + 1) := bernsteinNumber_nonneg T (k + 1)
      set s : ℝ := gelfand T (k + 1) with hs
      rcases le_or_gt s 0 with hs0 | hspos
      · exact le_trans hs0 (by positivity)
      -- `ρ_k > 0`, else the induction hypothesis forces `s ≤ 0`
      have hρk : 0 < bernsteinNumber T k := by
        rcases (bernsteinNumber_nonneg T k).lt_or_eq with h | h
        · exact h
        · exfalso
          rw [← h, mul_zero] at ih'
          have := le_trans (gelfand_succ_le T k) ih'
          linarith
      have hsCk : s / Ck ≤ bernsteinNumber T k := by
        rw [div_le_iff₀ hCkpos]
        have := le_trans (gelfand_succ_le T k) ih'
        nlinarith
      have hsle : s / Ck ≤ s := by
        rw [div_le_iff₀ hCkpos]
        nlinarith
      -- the `ε → 0` limit
      have hkey : s / Ck ≤ 2 * ((k : ℝ) + 1) * bernsteinNumber T (k + 1) := by
        refine le_of_forall_pos_le_add fun δ hδ => ?_
        set ε : ℝ := min (min (δ * Ck / s) δ) (min (1 / 2) (s / 2)) with hε
        have hεpos : 0 < ε := by
          refine lt_min (lt_min (by positivity) hδ) (lt_min (by norm_num) (by positivity))
        have hε1 : ε < 1 := lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _))
          (by norm_num)
        have hεs : ε < s := lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _))
          (by linarith)
        have hεδ : ε ≤ δ := le_trans (min_le_left _ _) (min_le_right _ _)
        have hεCk : ε ≤ δ * Ck / s := le_trans (min_le_left _ _) (min_le_left _ _)
        have hstep := bernstein_succ_ge_of_eps T hk1 hεpos hε1 hεs hρk
        have hA : s / Ck - δ ≤ (1 - ε) * bernsteinNumber T k := by
          have h1 : (1 - ε) * (s / Ck) ≤ (1 - ε) * bernsteinNumber T k :=
            mul_le_mul_of_nonneg_left hsCk (by linarith)
          have h2 : ε * (s / Ck) ≤ δ := by
            have : ε * s ≤ δ * Ck := by
              have := mul_le_mul_of_nonneg_right hεCk hspos.le
              rwa [div_mul_cancel₀ _ (ne_of_gt hspos)] at this
            rw [mul_div_assoc'] at *
            rw [div_le_iff₀ hCkpos]
            nlinarith
          nlinarith
        have hB : s / Ck - δ ≤ s - ε := by linarith
        have := le_trans (le_min hA hB) hstep
        linarith
      have : s ≤ Ck * (2 * ((k : ℝ) + 1) * bernsteinNumber T (k + 1)) := by
        rw [← div_le_iff₀' hCkpos]
        exact hkey
      calc s ≤ Ck * (2 * ((k : ℝ) + 1) * bernsteinNumber T (k + 1)) := this
        _ = (2 * ((k : ℝ) + 1) * Ck) * bernsteinNumber T (k + 1) := by ring
        _ ≤ Ck1 * bernsteinNumber T (k + 1) := mul_le_mul_of_nonneg_right hratio hρnn

/-- A continuous rank-one map is a compact operator: it factors through `ℝ`, which is locally
compact. -/
theorem isCompactOperator_smulRight (g : X →L[ℝ] ℝ) (y : X) :
    IsCompactOperator ((g.smulRight y : X →L[ℝ] X) : X → X) := by
  have hg : IsCompactOperator (g : X → ℝ) := isCompactOperator_of_locallyCompactSpace_dom g
  have h2 := hg.clm_comp (ContinuousLinearMap.toSpanSingleton ℝ y)
  have heq : ((ContinuousLinearMap.toSpanSingleton ℝ y : ℝ →L[ℝ] X) ∘ (g : X → ℝ))
      = ((g.smulRight y : X →L[ℝ] X) : X → X) := by
    funext x
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  rwa [heq] at h2

/-- **A projection with prescribed kernel and controlled norm.** If `V` is closed of finite
codimension `m`, there is a continuous `P` with `x - P x ∈ V` for every `x`, of finite rank, and
with `‖P‖ ≤ 2m`.

This is the Auerbach substitute for the theorem of Kadec used in the appendix of
`proof_met.tex`: Kadec gives a complement with `‖Π_{V‖W}‖ ≤ √m + ε`, whereas an Auerbach basis of
the *quotient* `X ⧸ V`, lifted back to `X` at the cost of a factor `2`, gives `2m`. Only the
constant differs. -/
theorem exists_proj_sub_mem (V : Submodule ℝ X) (hVc : IsClosed (V : Set X))
    [FiniteDimensional ℝ (X ⧸ V)] {m : ℕ} (hm : Module.finrank ℝ (X ⧸ V) = m) :
    ∃ P : X →L[ℝ] X, (∀ x, x - P x ∈ V) ∧ IsCompactOperator (P : X → X) ∧ ‖P‖ ≤ 2 * m := by
  classical
  have : IsClosed ((V : Submodule ℝ X) : Set X) := hVc
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · -- `V = ⊤`, take `P = 0`
    have hsub : Subsingleton (X ⧸ V) := Module.finrank_zero_iff.1 hm
    have htop : V = ⊤ := Submodule.Quotient.subsingleton_iff.1 hsub
    refine ⟨0, fun x => by simp [htop], isCompactOperator_zero, by simp⟩
  obtain ⟨e, henorm, hcond⟩ := exists_auerbach_basis (E := X ⧸ V) hm
  have hind : LinearIndependent ℝ e :=
    linearIndependent_of_norm_coeff_le (C := 1) (fun a => by simpa using hcond a)
  have : Nonempty (Fin m) := ⟨⟨0, hmpos⟩⟩
  set b : Module.Basis (Fin m) ℝ (X ⧸ V) :=
    basisOfLinearIndependentOfCardEqFinrank hind (by simp [hm]) with hb
  have hbe : ⇑b = e := coe_basisOfLinearIndependentOfCardEqFinrank hind (by simp [hm])
  -- the coordinate functionals of an Auerbach basis have norm at most one
  have hcoord : ∀ (i : Fin m) (q : X ⧸ V), |b.coord i q| ≤ ‖q‖ := by
    intro i q
    have hsum : ∑ j, b.equivFun q j • e j = q := by rw [← hbe]; exact b.sum_equivFun q
    have h1 : |b.equivFun q i| ≤ ‖b.equivFun q‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (b.equivFun q) i
    have h2 : ‖b.equivFun q‖ ≤ ‖∑ j, b.equivFun q j • e j‖ := hcond _
    rw [hsum] at h2
    have h3 : b.coord i q = b.equivFun q i := by simp [Basis.coord_apply, Basis.equivFun_apply]
    rw [h3]; linarith
  -- pull the coordinate functionals back to `X`, and lift the basis vectors
  have hfex : ∀ i : Fin m, ∃ f : X →L[ℝ] ℝ,
      (∀ x, f x = b.coord i (Submodule.Quotient.mk x)) ∧ ‖f‖ ≤ 1 := by
    intro i
    set π : X →L[ℝ] (X ⧸ V) := (V.mkQ).mkContinuous 1 (fun x => by
      simpa using Submodule.Quotient.norm_mk_le V x) with hπ
    refine ⟨(LinearMap.toContinuousLinearMap (b.coord i)).comp π, fun x => rfl, ?_⟩
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    have hπx : π x = (Submodule.Quotient.mk x : X ⧸ V) := rfl
    have h1 : ‖((LinearMap.toContinuousLinearMap (b.coord i)).comp π) x‖
        = |b.coord i (Submodule.Quotient.mk x : X ⧸ V)| := by
      rw [ContinuousLinearMap.comp_apply, hπx]
      simp [Real.norm_eq_abs]
    rw [h1]
    exact (hcoord i _).trans (Submodule.Quotient.norm_mk_le V x)
  choose f hfapp hfnorm using hfex
  have hwex : ∀ i : Fin m, ∃ w : X, Submodule.Quotient.mk w = e i ∧ ‖w‖ ≤ 2 := by
    intro i
    obtain ⟨w, hw, hwlt⟩ := Submodule.Quotient.norm_mk_lt (e i) (by norm_num : (0:ℝ) < 1)
    exact ⟨w, hw, by rw [henorm i] at hwlt; linarith⟩
  choose w hwmk hwnorm using hwex
  refine ⟨∑ i, (f i).smulRight (w i), ?_, ?_, ?_⟩
  · intro x
    rw [← Submodule.Quotient.mk_eq_zero]
    have happ : (∑ i, (f i).smulRight (w i)) x = ∑ i, f i x • w i := by
      simp [ContinuousLinearMap.smulRight_apply]
    rw [happ, Submodule.Quotient.mk_sub]
    have hmk : (Submodule.Quotient.mk (∑ i, f i x • w i) : X ⧸ V)
        = ∑ i, b.coord i (Submodule.Quotient.mk x) • e i := by
      have hms : (Submodule.Quotient.mk (∑ i, f i x • w i) : X ⧸ V)
          = ∑ i, V.mkQ (f i x • w i) := by
        rw [← Submodule.mkQ_apply]; exact map_sum V.mkQ _ _
      rw [hms]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Submodule.mkQ_apply, hwmk i, hfapp i]
    rw [hmk]
    have hrepr : ∑ i, b.coord i (Submodule.Quotient.mk x : X ⧸ V) • e i
        = (Submodule.Quotient.mk x : X ⧸ V) := by
      rw [← hbe]
      simp [Basis.coord_apply]
    rw [hrepr, sub_self]
  · have hsum : ∀ s : Finset (Fin m),
        IsCompactOperator (((∑ i ∈ s, (f i).smulRight (w i)) : X →L[ℝ] X) : X → X) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          have h0 : (((∑ i ∈ (∅ : Finset (Fin m)), (f i).smulRight (w i)) : X →L[ℝ] X) : X → X)
              = (0 : X → X) := by funext x; simp
          rw [h0]
          exact isCompactOperator_zero
      | insert i s hi ih =>
          have heq : (((∑ j ∈ insert i s, (f j).smulRight (w j)) : X →L[ℝ] X) : X → X)
              = ((((f i).smulRight (w i)) : X →L[ℝ] X) : X → X)
                + (((∑ j ∈ s, (f j).smulRight (w j)) : X →L[ℝ] X) : X → X) := by
            funext x; simp [Finset.sum_insert hi]
          rw [heq]
          exact (isCompactOperator_smulRight (f i) (w i)).add ih
    exact hsum Finset.univ
  · refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i : Fin m, ‖(f i).smulRight (w i)‖ ≤ 2 := by
      intro i
      rw [ContinuousLinearMap.norm_smulRight_apply]
      calc ‖f i‖ * ‖w i‖ ≤ 1 * 2 := by
            exact mul_le_mul (hfnorm i) (hwnorm i) (norm_nonneg _) zero_le_one
        _ = 2 := by norm_num
    calc ∑ i, ‖(f i).smulRight (w i)‖ ≤ ∑ _i : Fin m, (2 : ℝ) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = 2 * m := by simp [mul_comm]

theorem compactSeminorm_nonneg (T : X →L[ℝ] X) : 0 ≤ compactSeminorm T := by
  refine Real.sInf_nonneg ?_
  rintro _ ⟨K, -, rfl⟩
  exact norm_nonneg _

theorem compactSeminorm_le {T K : X →L[ℝ] X} (hK : IsCompactOperator (K : X → X)) :
    compactSeminorm T ≤ ‖T - K‖ :=
  csInf_le ⟨0, by rintro _ ⟨K', -, rfl⟩; exact norm_nonneg _⟩ ⟨K, hK, rfl⟩

/-- In a finite-dimensional space every operator is compact, so the seminorm vanishes. -/
theorem compactSeminorm_eq_zero_of_finiteDimensional [FiniteDimensional ℝ X] (T : X →L[ℝ] X) :
    compactSeminorm T = 0 := by
  refine le_antisymm ?_ (compactSeminorm_nonneg T)
  have hT : IsCompactOperator (T : X → X) := isCompactOperator_of_locallyCompactSpace_dom T
  simpa using compactSeminorm_le (T := T) hT

/-- An infinite-dimensional space has subspaces of every finite codimension. -/
theorem nonempty_grassmannianCofin_of_infinite (hX : ¬ FiniteDimensional ℝ X) (j : ℕ) :
    Nonempty (GrassmannianCofin X j) := by
  have hrank : (j : Cardinal) ≤ Module.rank ℝ X := by
    have h1 : ¬ Module.rank ℝ X < Cardinal.aleph0 := by
      rw [Module.rank_lt_aleph0_iff]
      exact hX
    rw [not_lt] at h1
    exact le_trans (le_of_lt (Cardinal.natCast_lt_aleph0 (n := j))) h1
  obtain ⟨s, hcard, hind⟩ := le_rank_iff_exists_linearIndependent_finset.1 hrank
  set W : Submodule ℝ X := Submodule.span ℝ (s : Set X) with hW
  have : FiniteDimensional ℝ W := by
    rw [hW]; exact FiniteDimensional.span_of_finite ℝ s.finite_toSet
  have hWrank : Module.finrank ℝ W = j := by
    rw [hW, finrank_span_set_eq_card hind]
    simpa using hcard
  exact nonempty_grassmannianCofin W hWrank

/-- **`‖T‖_c ≤ 2k·s_k(T)`** (`proof_met.tex`, appendix), for `k ≥ 1`.

The paper states `s_k(T) ≥ k^{-1/2}‖T‖_c`, using the theorem of Kadets to choose a complement
`V ⊕ W = X` with `‖Π_{V‖W}‖ ≤ √(k-1) + ε`. Mathlib has neither Kadets' theorem nor
Kadec--Snobar, so `exists_proj_sub_mem` supplies instead a projection killing `V` of norm at most
`2(k-1)`, built from an Auerbach basis of the quotient `X ⧸ V` lifted back to `X`. Only the
constant changes, and the sole consumer (`nu_eq_compactnessIndex`) takes `(1/n) log`, where a
constant depending on `k` alone vanishes. -/
theorem compactSeminorm_le_gelfand (T : X →L[ℝ] X) {k : ℕ} (hk : 1 ≤ k) :
    compactSeminorm T ≤ 2 * (k : ℝ) * gelfand T k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hpos : (0 : ℝ) < 2 * ((j : ℝ) + 1) := by positivity
  rw [gelfand_succ T j]
  rcases isEmpty_or_nonempty (GrassmannianCofin X j) with hE | hne
  · -- no subspace of codimension `j`, so `X` is finite-dimensional and `T` is compact
    have hfd : FiniteDimensional ℝ X := by
      by_contra hcon
      exact (nonempty_grassmannianCofin_of_infinite hcon j).elim hE.elim
    rw [compactSeminorm_eq_zero_of_finiteDimensional, Set.range_eq_empty, Real.sInf_empty]
    norm_num
  · have hkey : ∀ V : GrassmannianCofin X j,
        compactSeminorm T ≤ 2 * ((j : ℝ) + 1) *
          ‖T.comp (V.1.1 : Submodule ℝ X).subtypeL‖ := by
      intro V
      have : FiniteDimensional ℝ (X ⧸ (V.1.1 : Submodule ℝ X)) := V.2.1
      obtain ⟨P, hPsub, hPcomp, hPnorm⟩ :=
        exists_proj_sub_mem (V.1.1 : Submodule ℝ X) V.1.2.isClosed V.2.2
      have hKcomp : IsCompactOperator ((T.comp P : X →L[ℝ] X) : X → X) := by
        have := hPcomp.clm_comp T
        exact this
      refine le_trans (compactSeminorm_le hKcomp) ?_
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
      have hval : (T - T.comp P) x = T (x - P x) := by simp [map_sub]
      have hmem : x - P x ∈ (V.1.1 : Submodule ℝ X) := hPsub x
      have h1 : ‖T (x - P x)‖ ≤ ‖T.comp (V.1.1 : Submodule ℝ X).subtypeL‖ * ‖x - P x‖ := by
        have := (T.comp (V.1.1 : Submodule ℝ X).subtypeL).le_opNorm ⟨x - P x, hmem⟩
        simpa using this
      have h2 : ‖x - P x‖ ≤ (2 * (j : ℝ) + 1) * ‖x‖ := by
        have hPx : ‖P x‖ ≤ 2 * (j : ℝ) * ‖x‖ := by
          refine le_trans (P.le_opNorm x) ?_
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hPnorm) (norm_nonneg x)
        calc ‖x - P x‖ ≤ ‖x‖ + ‖P x‖ := norm_sub_le _ _
          _ ≤ ‖x‖ + 2 * (j : ℝ) * ‖x‖ := by linarith
          _ = (2 * (j : ℝ) + 1) * ‖x‖ := by ring
      rw [hval]
      have hnn : 0 ≤ ‖T.comp (V.1.1 : Submodule ℝ X).subtypeL‖ :=
        norm_nonneg (T.comp (V.1.1 : Submodule ℝ X).subtypeL)
      calc ‖T (x - P x)‖ ≤ ‖T.comp (V.1.1 : Submodule ℝ X).subtypeL‖ * ‖x - P x‖ := h1
        _ ≤ ‖T.comp (V.1.1 : Submodule ℝ X).subtypeL‖ * ((2 * (j : ℝ) + 1) * ‖x‖) :=
            mul_le_mul_of_nonneg_left h2 hnn
        _ ≤ 2 * ((j : ℝ) + 1) * ‖T.comp (V.1.1 : Submodule ℝ X).subtypeL‖ * ‖x‖ := by
            nlinarith [norm_nonneg x, hnn]
    push_cast
    rw [← div_le_iff₀' hpos]
    refine le_csInf (Set.range_nonempty _) ?_
    rintro _ ⟨V, rfl⟩
    rw [div_le_iff₀' hpos]
    exact hkey V

namespace Measdisaster

open scoped ENNReal

/-- The `ℝ`-valued `±1` reading of a `{±1}`-coordinate: `true ↦ 1`, `false ↦ -1`. -/
def sgn (ω : ℤ → Bool) (i : ℤ) : ℝ := if ω i then 1 else -1

instance : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_refl _⟩

/-- The model space `ℓ¹(ℤ, ℝ)`. -/
abbrev Y : Type := lp (fun _ : ℤ => ℝ) 1

theorem sgn_norm (ω : ℤ → Bool) (i : ℤ) : ‖sgn ω i‖ = 1 := by
  unfold sgn; split <;> simp

theorem sgn_not (ω : ℤ → Bool) (i : ℤ) : sgn (fun j => !ω j) i = - sgn ω i := by
  rcases Bool.eq_false_or_eq_true (ω i) with h | h <;> simp [sgn, h]

theorem summable_sgn_mul (ω : ℤ → Bool) (x : Y) :
    Summable (fun i => sgn ω i * (x : lp _ 1) i) := by
  have hx : Summable (fun i => ‖(x : lp _ 1) i‖) := by
    have h := (lp.memℓp x).summable (p := 1) (by simp)
    simpa using h
  refine Summable.of_norm_bounded hx fun i => ?_
  rw [norm_mul, sgn_norm, one_mul]

/-- The bounded functional `x ↦ Σᵢ ωᵢ xᵢ` on `ℓ¹`, as a linear map. -/
noncomputable def phi (ω : ℤ → Bool) : Y →ₗ[ℝ] ℝ where
  toFun x := ∑' i, sgn ω i * (x : lp _ 1) i
  map_add' x y := by
    refine (tsum_congr fun i => ?_).trans
      ((summable_sgn_mul ω x).tsum_add (summable_sgn_mul ω y))
    rw [lp.coeFn_add, Pi.add_apply]; ring
  map_smul' c x := by
    simp only [RingHom.id_apply, smul_eq_mul]
    refine (tsum_congr fun i => ?_).trans tsum_mul_left
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; ring

theorem phi_apply (ω : ℤ → Bool) (x : Y) :
    phi ω x = ∑' i, sgn ω i * (x : lp _ 1) i := rfl

theorem phi_single (ω : ℤ → Bool) (k : ℤ) :
    phi ω (lp.single 1 k (1 : ℝ)) = sgn ω k := by
  rw [phi_apply, tsum_eq_single k]
  · rw [lp.single_apply, Pi.single_eq_same, mul_one]
  · intro m hm
    rw [lp.single_apply, Pi.single_eq_of_ne hm, mul_zero]

theorem phi_not (ω : ℤ → Bool) (x : Y) : phi (fun j => !ω j) x = - phi ω x := by
  rw [phi_apply, phi_apply, ← tsum_neg]
  refine tsum_congr fun i => ?_
  rw [sgn_not]; ring

/-- The codimension-one slow space `V_ω = ker φ_ω`. -/
noncomputable def V (ω : ℤ → Bool) : Submodule ℝ Y := LinearMap.ker (phi ω)

theorem mem_V {ω : ℤ → Bool} {x : Y} : x ∈ V ω ↔ phi ω x = 0 := LinearMap.mem_ker

theorem V_symm (ω : ℤ → Bool) : V ω = V (fun j => !ω j) := by
  ext x
  simp only [mem_V, phi_not, neg_eq_zero]

theorem norm_eq_tsum (x : Y) : ‖x‖ = ∑' i, |(x : lp _ 1) i| := by
  have h := lp.norm_rpow_eq_tsum (show (0 : ℝ) < (1 : ℝ≥0∞).toReal by simp) x
  simpa [Real.norm_eq_abs] using h

theorem phi_abs_le (ω : ℤ → Bool) (x : Y) : |phi ω x| ≤ ‖x‖ := by
  rw [phi_apply, ← Real.norm_eq_abs, norm_eq_tsum]
  refine (norm_tsum_le_tsum_norm ?_).trans_eq (tsum_congr fun i => ?_)
  · simpa only [Real.norm_eq_abs] using summable_abs_iff.mpr (summable_sgn_mul ω x)
  · rw [norm_mul, sgn_norm, one_mul, Real.norm_eq_abs]

theorem sgn_mul_self (ω : ℤ → Bool) (i : ℤ) : sgn ω i * sgn ω i = 1 := by
  unfold sgn; split <;> norm_num

theorem sgn_abs (ω : ℤ → Bool) (i : ℤ) : |sgn ω i| = 1 := by
  unfold sgn; split <;> norm_num

theorem phi_single' (ω : ℤ → Bool) (k : ℤ) (v : ℝ) :
    phi ω (lp.single 1 k v) = v * sgn ω k := by
  have hv : (lp.single 1 k v : Y) = v • (lp.single 1 k (1 : ℝ) : Y) := by
    rw [← lp.single_smul]; simp
  rw [hv, map_smul, phi_single, smul_eq_mul]

open Cardinal

/-- `φ_ω` as a bounded functional, `‖φ_ω‖ ≤ 1`. -/
noncomputable def phiL (ω : ℤ → Bool) : Y →L[ℝ] ℝ :=
  (phi ω).mkContinuous 1 fun x => by rw [one_mul, Real.norm_eq_abs]; exact phi_abs_le ω x

theorem phiL_apply (ω : ℤ → Bool) (x : Y) : phiL ω x = phi ω x := rfl

/-- `V_ω = ker φ_ω` is closed and complemented: `t ↦ t ω₀ e₀` is a bounded right inverse
of `φ_ω`. -/
theorem V_closedComplemented (ω : ℤ → Bool) : (V ω).ClosedComplemented := by
  refine (phiL ω).closedComplemented_ker_of_rightInverse
    ((1 : ℝ →L[ℝ] ℝ).smulRight (lp.single 1 0 (sgn ω 0))) fun t => ?_
  simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, map_smul,
    phiL_apply, phi_single', smul_eq_mul, sgn_mul_self, mul_one]

/-- `V_ω` as a point of `𝒢X`. -/
noncomputable def Vg (ω : ℤ → Bool) : Grassmannian Y := ⟨V ω, V_closedComplemented ω⟩

/-- If `ω` and `ω'` agree at `i` and differ at `j`, some unit vector of `V_ω` is at distance
`≥ 1` from `V_{ω'}`. -/
theorem far_of_agree_disagree {ω ω' : ℤ → Bool} {i j : ℤ} (hi : ω i = ω' i) (hj : ω j ≠ ω' j) :
    ∃ x ∈ (V ω : Set Y), ‖x‖ = 1 ∧ ∀ y ∈ (V ω' : Set Y), 1 ≤ ‖x - y‖ := by
  have hij : i ≠ j := by rintro rfl; exact hj hi
  have hsi : sgn ω' i = sgn ω i := by unfold sgn; rw [hi]
  have hsj : sgn ω' j = - sgn ω j := by
    unfold sgn; cases hb : ω' j <;> cases ha : ω j <;> simp_all
  set x : Y := lp.single 1 i ((1 : ℝ) / 2) + lp.single 1 j (-(sgn ω i * sgn ω j) / 2)
    with hx_def
  have hxi : (x : lp _ 1) i = 1 / 2 := by
    rw [hx_def, lp.coeFn_add, Pi.add_apply, lp.single_apply, lp.single_apply,
        Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero]
  have hxj : (x : lp _ 1) j = -(sgn ω i * sgn ω j) / 2 := by
    rw [hx_def, lp.coeFn_add, Pi.add_apply, lp.single_apply, lp.single_apply,
        Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_same, zero_add]
  have hphiω : phi ω x = 0 := by
    rw [hx_def, map_add, phi_single', phi_single']
    linear_combination (- sgn ω i / 2) * sgn_mul_self ω j
  have hphiω' : phi ω' x = sgn ω i := by
    rw [hx_def, map_add, phi_single', phi_single', hsi, hsj]
    linear_combination (sgn ω i / 2) * sgn_mul_self ω j
  have hcj_abs : |(-(sgn ω i * sgn ω j) / 2)| = 1 / 2 := by
    rw [abs_div, abs_neg, abs_mul, sgn_abs, sgn_abs]; norm_num
  have hxnorm : ‖x‖ = 1 := by
    have hsupp : ∀ k ∉ ({i, j} : Finset ℤ), |(x : lp _ 1) k| = 0 := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      obtain ⟨hki, hkj⟩ := hk
      rw [abs_eq_zero, hx_def, lp.coeFn_add, Pi.add_apply, lp.single_apply, lp.single_apply,
          Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj, add_zero]
    rw [norm_eq_tsum, tsum_eq_sum hsupp, Finset.sum_pair hij, hxi, hxj, hcj_abs]
    norm_num
  refine ⟨x, SetLike.mem_coe.mpr (mem_V.mpr hphiω), hxnorm, ?_⟩
  intro y hy
  rw [SetLike.mem_coe] at hy
  have hyV : phi ω' y = 0 := mem_V.mp hy
  have key : phi ω' (x - y) = sgn ω i := by
    rw [map_sub, hphiω', hyV, sub_zero]
  have hb := phi_abs_le ω' (x - y)
  rw [key] at hb
  calc (1 : ℝ) = |sgn ω i| := (sgn_abs ω i).symm
    _ ≤ ‖x - y‖ := hb

/-- Unless `ω' = ±ω`, the two agree somewhere and differ somewhere. -/
theorem exists_agree_disagree {ω ω' : ℤ → Bool} (h1 : ω' ≠ ω) (h2 : ω' ≠ fun j => !ω j) :
    ∃ i j, ω i = ω' i ∧ ω j ≠ ω' j := by
  have hdiff : ∃ j, ω j ≠ ω' j := by
    by_contra h
    exact h1 (funext fun j => (not_not.mp fun hj => h ⟨j, hj⟩).symm)
  have hagree : ∃ i, ω i = ω' i := by
    by_contra h
    exact h2 (funext fun j => by
      have hj : ω j ≠ ω' j := fun e => h ⟨j, e⟩
      cases hb : ω' j <;> cases ha : ω j <;> simp_all)
  obtain ⟨i, hi⟩ := hagree
  obtain ⟨j, hj⟩ := hdiff
  exact ⟨i, j, hi, hj⟩

/-- `V_ω = V_{ω'}` only for `ω' = ±ω`. -/
theorem eq_or_eq_not_of_V_eq {ω ω' : ℤ → Bool} (h : V ω = V ω') :
    ω' = ω ∨ ω' = fun j => !ω j := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨i, j, hi, hj⟩ := exists_agree_disagree hne.1 hne.2
  obtain ⟨x, hx, -, hfar⟩ := far_of_agree_disagree hi hj
  have h0 := hfar x (h ▸ hx)
  rw [sub_self, norm_zero] at h0
  exact absurd h0 (by norm_num)

/-- Distinct slow spaces are at distance at least `1` in `𝒢X`. -/
theorem one_le_edist_Vg {ω ω' : ℤ → Bool} (h : Vg ω ≠ Vg ω') : 1 ≤ edist (Vg ω) (Vg ω') := by
  have hV : V ω ≠ V ω' := fun e => h (Subtype.ext e)
  have h1 : ω' ≠ ω := by rintro rfl; exact hV rfl
  have h2 : ω' ≠ fun j => !ω j := by rintro rfl; exact hV (V_symm ω)
  obtain ⟨i, j, hi, hj⟩ := exists_agree_disagree h1 h2
  obtain ⟨x, hx, hn, hfar⟩ := far_of_agree_disagree hi hj
  rw [Grassmannian.edist_eq]
  have hxs : x ∈ (Vg ω).sphere := ⟨mem_sphere_zero_iff_norm.2 hn, hx⟩
  refine le_trans ?_ (Metric.infEDist_le_hausdorffEDist_of_mem hxs)
  rw [Metric.le_infEDist]
  rintro y ⟨-, hy⟩
  rw [edist_dist, dist_eq_norm]
  exact ENNReal.one_le_ofReal.2 (hfar y hy)

/-- If `ω ↦ V_ω` were measurable, every `±`-symmetric set would be measurable. -/
theorem measurableSet_of_symm (hW : Measurable Vg) (S : Set (ℤ → Bool))
    (hS : ∀ ω ∈ S, (fun j => !ω j) ∈ S) : MeasurableSet S := by
  have hcl : IsClosed (Vg '' S) := by
    refine isClosed_of_spaced_out (edist_mem_uniformity one_pos) ?_
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩ hne
    exact not_lt.2 (one_le_edist_Vg hne)
  have hpre : Vg ⁻¹' (Vg '' S) = S := by
    ext ω
    constructor
    · rintro ⟨a, ha, hVa⟩
      rcases eq_or_eq_not_of_V_eq (congrArg Subtype.val hVa) with h | h
      · exact h ▸ ha
      · exact h ▸ hS a ha
    · intro hω
      exact ⟨ω, hω, rfl⟩
  rw [← hpre]
  exact hW hcl.measurableSet

/-- The product `σ`-algebra on `{±1}^ℤ` has at most continuum many measurable sets. -/
theorem card_measurableSet_le :
    #{t : Set (ℤ → Bool) | MeasurableSet t} ≤ 𝔠 := by
  have hgen := MeasurableSpace.pi_eq_generateFrom_projections (α := fun _ : ℤ => Bool)
    (mα := fun _ => inferInstance)
  set s : Set (Set (ℤ → Bool)) :=
    {B | ∃ (i : ℤ) (t : Set Bool), MeasurableSet t ∧ Function.eval i ⁻¹' t = B}
  have hs : #s ≤ 𝔠 := by
    have hsub : s ⊆ Set.range fun p : ℤ × Set Bool => Function.eval p.1 ⁻¹' p.2 := by
      rintro _ ⟨i, t, -, rfl⟩
      exact ⟨(i, t), rfl⟩
    have hc : s.Countable := (Set.countable_range _).mono hsub
    exact (Cardinal.mk_le_aleph0_iff.2 hc.to_subtype).trans Cardinal.aleph0_le_continuum
  have := MeasurableSpace.cardinal_measurableSet_le_continuum hs
  convert this using 3
  rw [← hgen]

/-- Not every `±`-symmetric subset of `{±1}^ℤ` is measurable: there are `2^𝔠` of them. -/
theorem not_forall_symm_measurable :
    ¬ ∀ S : Set (ℤ → Bool), (∀ ω ∈ S, (fun j => !ω j) ∈ S) → MeasurableSet S := by
  intro hall
  set A : Set (ℤ → Bool) := {ω | ω 0 = true}
  let neg : (ℤ → Bool) → (ℤ → Bool) := fun ω j => !ω j
  let F : Set A → {t : Set (ℤ → Bool) | MeasurableSet t} := fun T =>
    ⟨Subtype.val '' T ∪ neg '' (Subtype.val '' T), hall _ (by
      rintro ω (hω | ⟨a, ha, rfl⟩)
      · exact Or.inr ⟨ω, hω, rfl⟩
      · left
        simpa [neg] using ha)⟩
  have hF : Function.Injective F := by
    intro T T' h
    have h' := congrArg (fun t : {t : Set (ℤ → Bool) | MeasurableSet t} => (t : Set _) ∩ A) h
    have key : ∀ T : Set A, (Subtype.val '' T ∪ neg '' (Subtype.val '' T)) ∩ A =
        Subtype.val '' T := by
      intro T
      ext ω
      constructor
      · rintro ⟨hω | ⟨a, ⟨b, -, rfl⟩, rfl⟩, hA⟩
        · exact hω
        · have hb0 : (b : ℤ → Bool) 0 = true := b.2
          exact absurd hA (by simp [A, neg, hb0])
      · rintro ⟨b, hb, rfl⟩
        exact ⟨Or.inl ⟨b, hb, rfl⟩, b.2⟩
    simp only [F, key] at h'
    exact Set.image_injective.2 Subtype.val_injective h'
  -- `#A ≥ 𝔠`
  let g : (ℕ → Bool) → A := fun x =>
    ⟨fun n => if 1 ≤ n then x (n - 1).toNat else true, by simp [A]⟩
  have hg : Function.Injective g := by
    intro x x' h
    funext m
    have := congrFun (congrArg Subtype.val h) ((m : ℤ) + 1)
    simpa [g] using this
  have hA : 𝔠 ≤ #A := by
    have := Cardinal.mk_le_of_injective hg
    rwa [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat,
      Cardinal.two_power_aleph0] at this
  have hle : 2 ^ 𝔠 ≤ 𝔠 :=
    calc 2 ^ 𝔠 ≤ 2 ^ #A := Cardinal.power_le_power_left two_ne_zero hA
      _ = #(Set A) := Cardinal.mk_set.symm
      _ ≤ #{t : Set (ℤ → Bool) | MeasurableSet t} := Cardinal.mk_le_of_injective hF
      _ ≤ 𝔠 := card_measurableSet_le
  exact absurd hle (not_le.2 (Cardinal.cantor 𝔠))

/-- `ℓ¹(ℤ)` is separable: finite combinations of unit vectors are dense. -/
instance : SeparableSpace Y := by
  set D : Set Y := Set.range fun i : ℤ => (lp.single 1 i (1 : ℝ) : Y)
  have hsep : IsSeparable (Submodule.span ℝ D : Set Y) := (Set.countable_range _).isSeparable.span
  have hdense : ∀ f : Y, f ∈ closure (Submodule.span ℝ D : Set Y) := by
    intro f
    refine mem_closure_of_tendsto (lp.hasSum_single (by simp) f) (Filter.Eventually.of_forall
      fun s => Submodule.sum_mem _ fun i _ => ?_)
    have : (lp.single 1 i (f i) : Y) = f i • (lp.single 1 i (1 : ℝ) : Y) := by
      rw [← lp.single_smul]; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [← isSeparable_univ_iff]
  exact hsep.closure.mono fun f _ => hdense f

/-- **Example \ref{measdisaster}** (Horan's counterexample, from J. A. Horan's PhD thesis,
University of Victoria, 2020, to the measurability claim of González-Tokman and Quas). On the
separable Banach space `ℓ¹(ℤ)`, every `V_ω = ker φ_ω` is a closed complemented subspace, but no
measurable map into `𝒢X` takes the value `V_ω` at every `ω ∈ {±1}^ℤ`: separability of `X`
alone does not make the slow spaces measurable. -/
theorem measdisaster :
    SeparableSpace Y ∧ (∀ ω, (V ω).ClosedComplemented) ∧
      ¬ ∃ W : (ℤ → Bool) → Grassmannian Y, Measurable W ∧ ∀ ω, (W ω).1 = V ω := by
  refine ⟨inferInstance, V_closedComplemented, ?_⟩
  rintro ⟨W, hW, hWV⟩
  have hWeq : W = Vg := funext fun ω => Subtype.ext (hWV ω)
  exact not_forall_symm_measurable fun S hS => measurableSet_of_symm (hWeq ▸ hW) S hS

end Measdisaster

end MultiplicativeErgodic
