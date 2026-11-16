/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2

public import LeanPool.MultiplicativeErgodic.GrowthFunction
public import LeanPool.MultiplicativeErgodic.MeasurableSelection

/-!
# Continuity, measurability, and contraction estimates on the Grassmannian

Remaining results of Section 3 of `proof_met.tex`, after the definition of
`growth`/`bernsteinNumber`.

Everything here uses the project's canonical structures on `GrassmannianFin X k`: the metric
induced by `grassmannianDist` and its Borel σ-algebra, both in `ProofMet.Grassmannian`. Earlier
drafts of this file took those as instance *hypotheses* instead, as stand-ins while the metric
was unproved; that turned out to make some of the statements false (instance-implicit binders
are universally quantified -- see `exists_measurable_retract_false` below), and the stand-ins
are all gone.
-/

@[expose] public section

namespace MultiplicativeErgodic

open TopologicalSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Lemma (continuity of `g`).** `g : 𝓑(X) × 𝒢_kX → [0,∞)` is continuous.

Proved directly via an ε-δ argument rather than the paper's route through uniform continuity
on the unit sphere: for `A, B ∈ 𝓑(X)` and `V, W ∈ 𝒢_kX` with `dist V W < δ`, take a minimizer
`x₀` of `‖A·‖` on the compact set `𝕊_V` (extreme value theorem), a nearby `y₀ ∈ 𝕊_W` with
`‖x₀ - y₀‖ < δ` (Hausdorff distance), and chain norm inequalities to get
`g_B(W) ≤ g_A(V) + (‖A‖ + ‖B - A‖) δ + ‖B - A‖`. Applying this with `(A, B) = (S₀, T)` and then
`(T, S₀)` and combining bounds both `g`s within `ε` of each other. -/
theorem growth_continuous (k : ℕ) [NeZero k] :
    Continuous (fun p : (X →L[ℝ] X) × GrassmannianFin X k =>
      growth p.1 (p.2.1 : Submodule ℝ X)) := by
  have key : ∀ (A B : X →L[ℝ] X) (V W : GrassmannianFin X k) (δ : ℝ), dist V W < δ →
      growth B (W.1 : Submodule ℝ X) ≤
        growth A (V.1 : Submodule ℝ X) + (‖A‖ + ‖B - A‖) * δ + ‖B - A‖ := by
    intro A B V W δ hδ
    have hcont : ContinuousOn (fun x => ‖A x‖) V.sphere := (A.continuous.norm).continuousOn
    obtain ⟨x₀, hx₀mem, hx₀min⟩ := V.isCompact_sphere.exists_isMinOn V.nonempty_sphere hcont
    have hgA : growth A (V.1 : Submodule ℝ X) = ‖A x₀‖ := by
      apply le_antisymm
      · exact csInf_le ⟨0, by rintro _ ⟨z, -, rfl⟩; exact norm_nonneg _⟩ ⟨x₀, hx₀mem, rfl⟩
      · have hne : ((fun x => ‖A x‖) '' V.sphere).Nonempty := ⟨‖A x₀‖, x₀, hx₀mem, rfl⟩
        apply le_csInf hne
        rintro _ ⟨y, hy, rfl⟩
        exact hx₀min hy
    have hhaus : Metric.hausdorffDist V.sphere W.sphere < δ := by
      rwa [← GrassmannianFin.dist_eq_hausdorffDist]
    have hfin : Metric.hausdorffEDist V.sphere W.sphere ≠ ⊤ :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded V.nonempty_sphere W.nonempty_sphere
        V.isCompact_sphere.isBounded W.isCompact_sphere.isBounded
    obtain ⟨y₀, hy₀mem, hy₀close⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hx₀mem hhaus hfin
    have hgB : growth B (W.1 : Submodule ℝ X) ≤ ‖B y₀‖ :=
      csInf_le ⟨0, by rintro _ ⟨z, -, rfl⟩; exact norm_nonneg _⟩ ⟨y₀, hy₀mem, rfl⟩
    have hx₀norm : ‖x₀‖ = 1 := mem_sphere_zero_iff_norm.1 hx₀mem.1
    have hBnorm : ‖B‖ ≤ ‖A‖ + ‖B - A‖ := by
      calc ‖B‖ = ‖A + (B - A)‖ := by rw [add_sub_cancel]
        _ ≤ ‖A‖ + ‖B - A‖ := norm_add_le _ _
    calc growth B (W.1 : Submodule ℝ X) ≤ ‖B y₀‖ := hgB
      _ = ‖B (y₀ - x₀) + B x₀‖ := by rw [map_sub, sub_add_cancel]
      _ ≤ ‖B (y₀ - x₀)‖ + ‖B x₀‖ := norm_add_le _ _
      _ ≤ ‖B‖ * ‖y₀ - x₀‖ + ‖B x₀‖ := by gcongr; exact B.le_opNorm _
      _ ≤ (‖A‖ + ‖B - A‖) * δ + ‖B x₀‖ := by
          gcongr
          rw [← dist_eq_norm, dist_comm]
          exact hy₀close.le
      _ = (‖A‖ + ‖B - A‖) * δ + ‖(B - A) x₀ + A x₀‖ := by
          rw [sub_apply, sub_add_cancel]
      _ ≤ (‖A‖ + ‖B - A‖) * δ + (‖(B - A) x₀‖ + ‖A x₀‖) := by gcongr; exact norm_add_le _ _
      _ ≤ (‖A‖ + ‖B - A‖) * δ + (‖B - A‖ * ‖x₀‖ + ‖A x₀‖) := by
          gcongr; exact (B - A).le_opNorm _
      _ = growth A (V.1 : Submodule ℝ X) + (‖A‖ + ‖B - A‖) * δ + ‖B - A‖ := by
          rw [hx₀norm, mul_one, hgA]; ring
  rw [Metric.continuous_iff]
  rintro ⟨S₀, V₀⟩ ε hε
  set δ := min 1 (ε / (2 * (‖S₀‖ + 3))) with hδdef
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  refine ⟨δ, hδpos, ?_⟩
  rintro ⟨T, W⟩ hdist
  rw [Prod.dist_eq, max_lt_iff] at hdist
  obtain ⟨hTS, hWV⟩ := hdist
  have hTS0 : ‖T - S₀‖ ≤ δ := (by rwa [dist_eq_norm] at hTS : ‖T - S₀‖ < δ).le
  have hS0T : ‖S₀ - T‖ ≤ δ := by rwa [norm_sub_rev]
  have hδle1 : δ ≤ 1 := min_le_left _ _
  have hδle2 : δ ≤ ε / (2 * (‖S₀‖ + 3)) := min_le_right _ _
  have hS0nn : (0:ℝ) ≤ ‖S₀‖ := norm_nonneg _
  have hδbound : (‖S₀‖ + 3) * δ ≤ ε / 2 := by
    have h3 : (0:ℝ) < ‖S₀‖ + 3 := by linarith
    calc (‖S₀‖ + 3) * δ ≤ (‖S₀‖ + 3) * (ε / (2 * (‖S₀‖ + 3))) :=
          mul_le_mul_of_nonneg_left hδle2 h3.le
      _ = ε / 2 := by field_simp
  have hTnorm : ‖T‖ ≤ ‖S₀‖ + 1 := by
    have h := norm_sub_norm_le T S₀
    linarith [hTS0, hδle1]
  change dist (growth T (W.1 : Submodule ℝ X)) (growth S₀ (V₀.1 : Submodule ℝ X)) < ε
  rw [Real.dist_eq, abs_lt]
  have h1 := key S₀ T V₀ W δ (by rwa [dist_comm] at hWV)
  have h2 := key T S₀ W V₀ δ hWV
  have e1 : ‖T - S₀‖ * δ ≤ δ * δ := mul_le_mul_of_nonneg_right hTS0 hδpos.le
  have e2 : ‖S₀ - T‖ * δ ≤ δ * δ := mul_le_mul_of_nonneg_right hS0T hδpos.le
  have e3 : δ * δ ≤ δ * 1 := mul_le_mul_of_nonneg_left hδle1 hδpos.le
  have hb1 : (‖S₀‖ + ‖T - S₀‖) * δ + ‖T - S₀‖ ≤ (‖S₀‖ + 3) * δ := by
    nlinarith [e1, e3, hTS0, hδle1]
  have hb2 : (‖T‖ + ‖S₀ - T‖) * δ + ‖S₀ - T‖ ≤ (‖S₀‖ + 3) * δ := by
    nlinarith [e2, e3, hS0T, hδle1, hTnorm, hδpos.le]
  have hfinal : (‖S₀‖ + 3) * δ < ε := by nlinarith [hδbound, hε]
  exact ⟨by linarith [h2, hb2, hfinal], by linarith [h1, hb1, hfinal]⟩

/-- **`ρ_k` is computed by any dense family of subspaces.** Extracted from the proof of
`bernstein_measurable`, which needed it only for a countable dense `D`; the statement is the
same for any dense `D` and is what the strongly-measurable version of that corollary reuses. -/
theorem bernsteinNumber_eq_ciSup_dense (k : ℕ) [NeZero k]
    (T : X →L[ℝ] X) {D : Set (GrassmannianFin X k)} (hDdense : Dense D) [Nonempty D] :
    bernsteinNumber T k = ⨆ V : D, growth T ((V : GrassmannianFin X k).1 : Submodule ℝ X) := by
  have hcontV : Continuous fun V : GrassmannianFin X k =>
      growth T (V.1 : Submodule ℝ X) :=
    (growth_continuous k).comp (continuous_const.prodMk continuous_id)
  have hbdd : BddAbove (Set.range fun V : GrassmannianFin X k => growth T (V.1 : Submodule ℝ X)) :=
    ⟨‖T‖, by rintro _ ⟨V, rfl⟩; exact growth_le_opNorm T V.1⟩
  have hbddD : BddAbove
      (Set.range fun V : D => growth T ((V : GrassmannianFin X k).1 : Submodule ℝ X)) :=
    ⟨‖T‖, by rintro _ ⟨V, rfl⟩; exact growth_le_opNorm T (V : GrassmannianFin X k).1⟩
  have : Nonempty (GrassmannianFin X k) := ⟨((Classical.arbitrary D : D) : GrassmannianFin X k)⟩
  unfold bernsteinNumber
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨V, rfl⟩
    by_contra hcon
    rw [not_le] at hcon
    set S := ⨆ V' : D, growth T ((V' : GrassmannianFin X k).1 : Submodule ℝ X) with hSdef
    set ε := growth T (V.1 : Submodule ℝ X) - S with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; linarith
    have hopen : IsOpen {V' : GrassmannianFin X k |
        growth T (V.1 : Submodule ℝ X) - ε < growth T V'.1} :=
      isOpen_lt continuous_const hcontV
    have hVmem : V ∈ {V' : GrassmannianFin X k |
        growth T (V.1 : Submodule ℝ X) - ε < growth T V'.1} := by
      change growth T (V.1 : Submodule ℝ X) - ε < growth T (V.1 : Submodule ℝ X)
      linarith
    obtain ⟨V', hV'D, hV'mem⟩ := hDdense.exists_mem_open hopen ⟨V, hVmem⟩
    have hle : growth T ((⟨V', hV'D⟩ : D) : GrassmannianFin X k).1 ≤ S :=
      le_ciSup hbddD ⟨V', hV'D⟩
    have hlt : growth T (V.1 : Submodule ℝ X) - ε < growth T V'.1 := hV'mem
    rw [hεdef] at hlt
    simp only at hle
    linarith
  · apply ciSup_le
    rintro ⟨V, hVD⟩
    exact le_csSup hbdd ⟨V, rfl⟩

/-- **Corollary.** The Bernstein numbers `ρ_k : 𝓑(X) → ℝ` are measurable.

Measurable for the *norm* topology on `𝓑(X)`; the strong-operator-topology version a cocycle
needs is `measurable_bernstein_of_weak` in `ProofMet/StrongMeasurability.lean`. Given
`grassmannianFin_separable`, `ρ_k(T)` is a supremum over a *countable* dense family of subspaces
(`bernsteinNumber_eq_ciSup_dense`), and a countable sup of continuous-in-`T` functions is
measurable. -/
theorem bernstein_measurable [SeparableSpace X] (k : ℕ) [NeZero k]
    [Nonempty (GrassmannianFin X k)] :
    Measurable (fun T : X →L[ℝ] X => bernsteinNumber T k) := by
  have := grassmannianFin_separable (X := X) k
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense (GrassmannianFin X k)
  have : Countable D := hDcount.to_subtype
  have : Nonempty D := by
    obtain ⟨V, hV, -⟩ := hDdense.exists_mem_open isOpen_univ Set.univ_nonempty
    exact ⟨⟨V, hV⟩⟩
  have hcontT : ∀ V : GrassmannianFin X k,
      Continuous fun T : X →L[ℝ] X => growth T (V.1 : Submodule ℝ X) :=
    fun V => (growth_continuous k).comp (continuous_id.prodMk continuous_const)
  simp_rw [fun T : X →L[ℝ] X => bernsteinNumber_eq_ciSup_dense k T hDdense]
  exact Measurable.iSup fun V => (hcontT _).measurable

/-- The pushforward `TV` of a `k`-dimensional subspace `V` along `T`, packaged as an element of
`𝒢_kX`, given that `T` grows `V` at a positive rate (which makes `T` injective on `V`, so the
image stays `k`-dimensional: `LinearMap.finrank_range_of_inj` transported along
`LinearMap.range_domRestrict`). -/
noncomputable def GrassmannianFin.pushforward {k : ℕ} (T : X →L[ℝ] X) (V : GrassmannianFin X k)
    (h : 0 < growth T (V.1 : Submodule ℝ X)) : GrassmannianFin X k :=
  ⟨(V.1 : Submodule ℝ X).map (T.toLinearMap), by
    have : FiniteDimensional ℝ (V.1 : Submodule ℝ X) := V.2.1
    have hinj := injective_domRestrict_of_growth_pos h
    refine ⟨inferInstance, ?_⟩
    have hrange := LinearMap.finrank_range_of_inj hinj
    rw [LinearMap.range_domRestrict] at hrange
    exact hrange.trans V.2.2⟩

/-- **Lemma \ref{pushclose} (Grassmannian contraction estimate).** If `ρ_{k+1}(T) < ρ_k(T)`,
`Θ ∈ (ρ_{k+1}(T), ρ_k(T))`, and `V, W ∈ 𝒢_kX` both grow faster than `Θ` under `T`, then the
images `TV` and `TW` (packaged via `GrassmannianFin.pushforward`, using that `Θ`-fastness makes
`T` injective on each of `V, W`) are close in the metric on `𝒢_kX`, quantitatively in terms of
`ρ_{k+1}(T)/Θ`.

Two corrections from the informal statement, both forced by making the claim actually true and
provable against this file's `dist`/`GrassmannianFin` infrastructure (`dist_eq_hausdorffDist`:
`dist` on `𝒢_kX` is the Hausdorff distance between *unit spheres*, not between the raw
subspaces): (1) `≤` instead of strict `<` -- equality is approached (e.g. `V = W` together with
`ρ_{k+1}(T) = 0` gives `dist = 0` against a bound of exactly `0`); (2) the constant is `4`, not
`2` -- the paper's inline estimate `‖Tc‖ ≤ ‖a‖ρ_{k+1}(T)`-chain bounds the distance from a point of
`TV` to the *subspace* `TW` by `2/(1-ρ_{k+1}(T)/Θ)·(ρ_{k+1}(T)/Θ)`, and renormalizing the nearest
subspace point back onto the unit sphere of `TW` (needed for an actual Hausdorff-distance-of-
spheres bound) costs a further factor of `2` in general Banach spaces (no inner product to make
that renormalization free), doubling the constant. -/
theorem pushclose (k : ℕ) [NeZero k] (T : X →L[ℝ] X) (Θ : ℝ) (hΘ : bernsteinNumber T (k + 1) < Θ)
    (V W : GrassmannianFin X k)
    (hV : Θ < growth T (V.1 : Submodule ℝ X)) (hW : Θ < growth T (W.1 : Submodule ℝ X)) :
    dist (GrassmannianFin.pushforward T V
            (lt_of_le_of_lt (bernsteinNumber_nonneg T (k + 1)) (hΘ.trans hV)))
         (GrassmannianFin.pushforward T W
            (lt_of_le_of_lt (bernsteinNumber_nonneg T (k + 1)) (hΘ.trans hW))) ≤
      4 / (1 - bernsteinNumber T (k + 1) / Θ) * (bernsteinNumber T (k + 1) / Θ) := by
  set ρ := bernsteinNumber T (k + 1) with hρdef
  have hρnonneg : 0 ≤ ρ := bernsteinNumber_nonneg T (k + 1)
  have hΘpos : 0 < Θ := lt_of_le_of_lt hρnonneg hΘ
  set x := ρ / Θ with hxdef
  have hxnonneg : 0 ≤ x := div_nonneg hρnonneg hΘpos.le
  have hxlt1 : x < 1 := (div_lt_one hΘpos).2 hΘ
  set bound := 4 / (1 - x) * x with hbounddef
  have hboundnonneg : 0 ≤ bound := by
    rw [hbounddef]
    have : (0:ℝ) < 1 - x := by linarith
    positivity
  -- The one-directional estimate: every point of `TV`'s sphere is within `bound` of `TW`'s sphere.
  -- Applied to `(V, W)` and (by symmetry) to `(W, V)` to get the two-sided Hausdorff bound.
  have key : ∀ (V W : GrassmannianFin X k) (hVpos : 0 < growth T (V.1 : Submodule ℝ X))
      (hWpos : 0 < growth T (W.1 : Submodule ℝ X)) (hV' : Θ < growth T (V.1 : Submodule ℝ X))
      (hW' : Θ < growth T (W.1 : Submodule ℝ X)),
      ∀ z ∈ (GrassmannianFin.pushforward T V hVpos).sphere,
        ∃ y ∈ (GrassmannianFin.pushforward T W hWpos).sphere, dist z y ≤ bound := by
    intro V W hVpos hWpos hV' hW' z hz
    obtain ⟨hzunit, a, haV, hTa⟩ := hz
    by_cases haW : a ∈ (W.1 : Submodule ℝ X)
    · exact ⟨z, ⟨hzunit, a, haW, hTa⟩, by rw [dist_self]; exact hboundnonneg⟩
    · have ha0 : a ≠ 0 := fun h => haW (h ▸ (W.1 : Submodule ℝ X).zero_mem)
      have : FiniteDimensional ℝ (W.1 : Submodule ℝ X) := W.2.1
      set U : Submodule ℝ X := (W.1 : Submodule ℝ X) ⊔ Submodule.span ℝ {a} with hUdef
      have hinf : (W.1 : Submodule ℝ X) ⊓ Submodule.span ℝ {a} = ⊥ :=
        disjoint_iff.mp ((Submodule.disjoint_span_singleton' ha0).2 haW)
      have hUfin : FiniteDimensional ℝ U := Submodule.finiteDimensional_sup _ _
      have hUrank : Module.finrank ℝ U = k + 1 := by
        have hsum := Submodule.finrank_sup_add_finrank_inf_eq
          (W.1 : Submodule ℝ X) (Submodule.span ℝ ({a} : Set X))
        rw [hinf, finrank_bot, add_zero, W.2.2, finrank_span_singleton ha0] at hsum
        exact hsum
      set Ufin : GrassmannianFin X (k + 1) := ⟨U, hUfin, hUrank⟩ with hUfindef
      have hgU : growth T U ≤ ρ :=
        le_csSup ⟨‖T‖, by rintro _ ⟨V', rfl⟩; exact growth_le_opNorm T V'.1⟩ ⟨Ufin, rfl⟩
      have hcont : ContinuousOn (fun y => ‖T y‖) Ufin.sphere := T.continuous.norm.continuousOn
      obtain ⟨c0, hc0mem, hc0min⟩ := Ufin.isCompact_sphere.exists_isMinOn Ufin.nonempty_sphere hcont
      have hgU_eq : growth T U = ‖T c0‖ := by
        apply le_antisymm
        · exact csInf_le ⟨0, by rintro _ ⟨z', -, rfl⟩; exact norm_nonneg _⟩ ⟨c0, hc0mem, rfl⟩
        · have hne : ((fun y => ‖T y‖) '' Ufin.sphere).Nonempty := ⟨‖T c0‖, c0, hc0mem, rfl⟩
          exact le_csInf hne (fun _ ⟨y, hy, hyeq⟩ => hyeq ▸ hc0min hy)
      have hc0U : c0 ∈ U := hc0mem.2
      rw [hUdef, Submodule.mem_sup] at hc0U
      obtain ⟨w, hwW, v, hvspan, hc0eq⟩ := hc0U
      rw [Submodule.mem_span_singleton] at hvspan
      obtain ⟨t, htv⟩ := hvspan
      have hc0norm : ‖c0‖ = 1 := mem_sphere_zero_iff_norm.1 hc0mem.1
      have hzunit1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hzunit
      have hTaz : T a = z := hTa
      have hTanorm : ‖T a‖ = 1 := by rw [hTaz, hzunit1]
      have htne : t ≠ 0 := by
        intro ht0
        rw [ht0, zero_smul] at htv
        have hc0W : c0 ∈ (W.1 : Submodule ℝ X) := by rw [← hc0eq, ← htv, add_zero]; exact hwW
        have : growth T (W.1 : Submodule ℝ X) ≤ ‖T c0‖ :=
          csInf_le ⟨0, by rintro _ ⟨z', -, rfl⟩; exact norm_nonneg _⟩
            ⟨c0, ⟨mem_sphere_zero_iff_norm.2 hc0norm, hc0W⟩, rfl⟩
        rw [← hgU_eq] at this
        linarith
      set b : X := -(t⁻¹ • w) with hbdef
      have hbW : b ∈ (W.1 : Submodule ℝ X) :=
        (W.1 : Submodule ℝ X).neg_mem ((W.1 : Submodule ℝ X).smul_mem _ hwW)
      have hc : a - b = t⁻¹ • c0 := by
        rw [hbdef, sub_neg_eq_add, ← hc0eq, ← htv, smul_add, smul_smul, inv_mul_cancel₀ htne,
          one_smul, add_comm a (t⁻¹ • w)]
      set c : X := a - b with hcdef
      have hTc : T c = t⁻¹ • T c0 := by rw [hc, map_smul]
      have hcnorm : ‖c‖ = ‖t‖⁻¹ := by rw [hc, norm_smul, norm_inv, hc0norm, mul_one]
      have hTcnorm_eq : ‖T c‖ = ‖t‖⁻¹ * ‖T c0‖ := by rw [hTc, norm_smul, norm_inv]
      have hTc_eq : ‖T c‖ = ‖c‖ * growth T U := by rw [hTcnorm_eq, hcnorm, hgU_eq]
      have hTcle : ‖T c‖ ≤ ‖c‖ * ρ := by
        rw [hTc_eq]; exact mul_le_mul_of_nonneg_left hgU (norm_nonneg c)
      -- b = 0 is impossible: it would force `growth T U = 1/‖a‖ ≤ ρ` while `‖a‖ ≤ 1/Θ` gives
      -- `Θ ≤ ρ`, contradicting `hΘ`.
      have haΘ : ‖a‖ * Θ ≤ ‖T a‖ :=
        (mul_le_mul_of_nonneg_left hV'.le (norm_nonneg a)).trans
          (by simpa only [mul_comm] using growth_mul_norm_le T haV)
      have hbne : b ≠ 0 := by
        intro hb0
        have hw0 : w = 0 := by
          have hb0' : t⁻¹ • w = 0 := by rw [hbdef, neg_eq_zero] at hb0; exact hb0
          exact (smul_eq_zero.1 hb0').resolve_left (inv_ne_zero htne)
        have hc0a : c0 = t • a := by rw [← hc0eq, htv, hw0, zero_add]
        have hgUval : growth T U = ‖t‖ := by
          rw [hgU_eq, hc0a, map_smul, hTaz, norm_smul, hzunit1, mul_one]
        have htnorm : ‖t‖ * ‖a‖ = 1 := by
          have h1 : ‖c0‖ = ‖t‖ * ‖a‖ := by rw [hc0a, norm_smul]
          rw [hc0norm] at h1; exact h1.symm
        have hΘlea : Θ ≤ 1 / ‖a‖ := by
          rw [le_div_iff₀ (norm_pos_iff.2 ha0)]
          linarith [haΘ, hTanorm]
        have hainv : 1 / ‖a‖ ≤ ρ := by
          rw [div_le_iff₀ (norm_pos_iff.2 ha0)]
          rw [hgUval] at hgU
          nlinarith [hgU, htnorm, norm_nonneg a]
        linarith [hΘ, hΘlea, hainv]
      have hTbeq : T b = T a - T c := by
        have hsub : T c = T a - T b := by rw [hcdef, map_sub]
        linear_combination (norm := module) hsub
      have : FiniteDimensional ℝ (W.1 : Submodule ℝ X) := W.2.1
      have hTbne : T b ≠ 0 := by
        intro hTb0
        have hinj := injective_domRestrict_of_growth_pos hWpos
        have : (⟨b, hbW⟩ : (W.1 : Submodule ℝ X)) = (⟨0, (W.1 : Submodule ℝ X).zero_mem⟩) := by
          apply hinj
          change T.toLinearMap b = T.toLinearMap 0
          rw [map_zero]; exact hTb0
        exact hbne (Subtype.ext_iff.1 this)
      have hbΘ : ‖b‖ * Θ ≤ ‖T b‖ :=
        (mul_le_mul_of_nonneg_left hW'.le (norm_nonneg b)).trans
          (by simpa only [mul_comm] using growth_mul_norm_le T hbW)
      -- the algebraic chain isolating `‖Tc‖ ≤ 2x/(1-x)` (paper's estimate, for the subspace `TW`)
      have hTbnorm_le : ‖T b‖ ≤ ‖T a‖ + ‖T c‖ := by
        rw [hTbeq]; exact norm_sub_le _ _
      have hcnorm_le : ‖c‖ ≤ ‖a‖ + ‖b‖ := by rw [hcdef]; exact norm_sub_le _ _
      have step1 : ‖T c‖ ≤ (‖a‖ + ‖b‖) * ρ := by
        calc ‖T c‖ ≤ ‖c‖ * ρ := hTcle
          _ ≤ (‖a‖ + ‖b‖) * ρ := mul_le_mul_of_nonneg_right hcnorm_le hρnonneg
      have step2 : ‖a‖ + ‖b‖ ≤ (‖T a‖ + ‖T b‖) / Θ := by
        rw [le_div_iff₀ hΘpos, add_mul]
        linarith [haΘ, hbΘ]
      have step3 : ‖T a‖ + ‖T b‖ ≤ 2 * ‖T a‖ + ‖T c‖ := by linarith [hTbnorm_le]
      have hepsbound : ‖T c‖ ≤ (2 * ‖T a‖ + ‖T c‖) * x := by
        calc ‖T c‖ ≤ (‖a‖ + ‖b‖) * ρ := step1
          _ ≤ ((‖T a‖ + ‖T b‖) / Θ) * ρ := mul_le_mul_of_nonneg_right step2 hρnonneg
          _ ≤ ((2 * ‖T a‖ + ‖T c‖) / Θ) * ρ := by
              gcongr
          _ = (2 * ‖T a‖ + ‖T c‖) * x := by rw [hxdef]; ring
      have hTcfinal : ‖T c‖ ≤ 2 * x / (1 - x) := by
        rw [le_div_iff₀ (by linarith)]
        nlinarith [hepsbound, hTanorm]
      -- normalize `T b` onto the unit sphere of `TW`, at a further cost of `‖Tc‖`
      set y : X := ‖T b‖⁻¹ • T b with hydef
      have hTbnorm_pos : 0 < ‖T b‖ := norm_pos_iff.2 hTbne
      have hyunit : ‖y‖ = 1 := by
        rw [hydef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hTbnorm_pos)]
      have hymem : y ∈ (GrassmannianFin.pushforward T W hWpos).1 := by
        change y ∈ (W.1 : Submodule ℝ X).map (T.toLinearMap)
        rw [hydef]
        exact Submodule.smul_mem _ _ ⟨b, hbW, rfl⟩
      refine ⟨y, ⟨mem_sphere_zero_iff_norm.2 hyunit, hymem⟩, ?_⟩
      rw [dist_eq_norm]
      have hstep_a : ‖z - T b‖ = ‖T c‖ := by
        rw [← hTaz, hTbeq]
        have : T a - (T a - T c) = T c := by abel
        rw [this]
      have hstep_b : ‖T b - y‖ ≤ ‖T c‖ := by
        have heq : T b - y = (1 - ‖T b‖⁻¹) • T b := by
          rw [hydef, sub_smul, one_smul]
        have hnorm_eq : ‖T b - y‖ = |1 - ‖T b‖⁻¹| * ‖T b‖ := by
          rw [heq, norm_smul, Real.norm_eq_abs]
        have hexpand : |1 - ‖T b‖⁻¹| * ‖T b‖ = |‖T b‖ - 1| := by
          have hcalc : (1 - ‖T b‖⁻¹) * ‖T b‖ = ‖T b‖ - 1 := by
            rw [sub_mul, one_mul, inv_mul_cancel₀ (ne_of_gt hTbnorm_pos)]
          calc |1 - ‖T b‖⁻¹| * ‖T b‖ = |1 - ‖T b‖⁻¹| * |‖T b‖| := by rw [abs_of_pos hTbnorm_pos]
            _ = |(1 - ‖T b‖⁻¹) * ‖T b‖| := (abs_mul _ _).symm
            _ = |‖T b‖ - 1| := by rw [hcalc]
        rw [hnorm_eq, hexpand]
        have hba : T b - T a = -T c := by rw [hTbeq]; abel
        have hbound := abs_norm_sub_norm_le (T b) (T a)
        rw [hTanorm, hba, norm_neg] at hbound
        exact hbound
      calc ‖z - y‖ ≤ ‖z - T b‖ + ‖T b - y‖ := norm_sub_le_norm_sub_add_norm_sub z (T b) y
        _ ≤ ‖T c‖ + ‖T c‖ := by linarith [hstep_a, hstep_b]
        _ = 2 * ‖T c‖ := by ring
        _ ≤ 2 * (2 * x / (1 - x)) := by linarith [hTcfinal]
        _ = bound := by rw [hbounddef]; ring
  rw [GrassmannianFin.dist_eq_hausdorffDist]
  exact Metric.hausdorffDist_le_of_mem_dist hboundnonneg
    (key V W _ _ hV hW) (key W V _ _ hW hV)

section SphereSelection

open Metric Filter TopologicalSpace Module

/-- Distance to the unit sphere of `V` is `1`-Lipschitz in `V`: the metric on `𝒢_kX` *is* the
Hausdorff distance between those spheres, so this is `infDist_le_infDist_add_hausdorffDist`
read twice. -/
theorem continuous_infDist_sphere (k : ℕ) [NeZero k] (x : X) :
    Continuous fun V : GrassmannianFin X k => infDist x V.sphere := by
  refine LipschitzWith.continuous (K := 1) ?_
  refine LipschitzWith.of_dist_le_mul fun V W => ?_
  have hfin : hausdorffEDist V.sphere W.sphere ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded V.nonempty_sphere W.nonempty_sphere
      V.isCompact_sphere.isBounded W.isCompact_sphere.isBounded
  have h1 : infDist x W.sphere ≤ infDist x V.sphere + hausdorffDist V.sphere W.sphere :=
    infDist_le_infDist_add_hausdorffDist hfin
  have h2 : infDist x V.sphere ≤ infDist x W.sphere + hausdorffDist W.sphere V.sphere :=
    infDist_le_infDist_add_hausdorffDist (by rwa [hausdorffEDist_comm] at hfin)
  rw [hausdorffDist_comm] at h2
  rw [Real.dist_eq, abs_sub_le_iff, GrassmannianFin.dist_eq_hausdorffDist]
  simp only [NNReal.coe_one, one_mul]
  exact ⟨by linarith, by linarith⟩

/-- The least index satisfying a measurable family of predicates is measurable. The
`∃`-form of this is `measurable_of_countable_cover`; this version names the function, which is
what a recursive greedy selection needs. -/
theorem measurable_sInf_of_measurable {Ω : Type*} [MeasurableSpace Ω] (P : ℕ → Ω → Prop)
    (hP : ∀ i, MeasurableSet {ω | P i ω}) (hne : ∀ ω, ∃ i, P i ω) :
    Measurable fun ω => sInf {i | P i ω} := by
  refine measurable_to_countable' fun i => ?_
  have hset : (fun ω => sInf {i | P i ω}) ⁻¹' {i}
      = {ω | P i ω} ∩ ⋂ l, ⋂ (_ : l < i), {ω | P l ω}ᶜ := by
    ext ω
    have hSne : {i | P i ω}.Nonempty := hne ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_compl_iff, Set.mem_ofPred_eq]
    constructor
    · rintro rfl
      refine ⟨Nat.sInf_mem hSne, fun l hl hlP => ?_⟩
      exact absurd (Nat.sInf_le (show l ∈ {i | P i ω} from hlP)) (not_le.2 hl)
    · rintro ⟨hi, hlt⟩
      have hle : sInf {i | P i ω} ≤ i := Nat.sInf_le (show i ∈ {i | P i ω} from hi)
      rcases lt_or_eq_of_le hle with h | h
      · exact absurd (Nat.sInf_mem hSne) (hlt _ h)
      · exact h
  rw [hset]
  exact (hP i).inter (MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ => (hP l).compl)

open scoped Classical in
/-- The greedy index sequence selecting a point of `𝕊_V`: at stage `j` it takes the first member
of the dense sequence `u` that is within `2^{-j}` of `𝕊_V` and within `2^{-j}+2^{-(j+1)}` of the
previous choice. Both conditions are measurable in `V` because `V ↦ d(x,𝕊_V)` is `1`-Lipschitz
(`continuous_infDist_sphere`) — the metric on `𝒢_kX` *is* the Hausdorff distance between the
spheres, so nothing here needs the family `{W ≤ V}`, which is where the older route stalled. -/
noncomputable def sphereSelIdx {k : ℕ} (u : ℕ → X) (V : GrassmannianFin X k)
    (j : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (sInf {i | infDist (u i) V.sphere < 1})
    (fun j prev => sInf {i | infDist (u i) V.sphere < (1 / 2 : ℝ) ^ (j + 1) ∧
      dist (u i) (u prev) < (1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ (j + 1)}) j

theorem sphereSelIdx_zero {k : ℕ} (u : ℕ → X) (V : GrassmannianFin X k) :
    sphereSelIdx u V 0 = sInf {i | infDist (u i) V.sphere < 1} := rfl

theorem sphereSelIdx_succ {k : ℕ} (u : ℕ → X) (V : GrassmannianFin X k) (j : ℕ) :
    sphereSelIdx u V (j + 1)
      = sInf {i | infDist (u i) V.sphere < (1 / 2 : ℝ) ^ (j + 1) ∧
          dist (u i) (u (sphereSelIdx u V j)) < (1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ (j + 1)} := rfl

/-- The greedy conditions are always satisfiable, and the selected index satisfies them. -/
theorem sphereSelIdx_spec {k : ℕ} [NeZero k] {u : ℕ → X} (hu : DenseRange u)
    (V : GrassmannianFin X k) : ∀ j : ℕ,
      infDist (u (sphereSelIdx u V j)) V.sphere < (1 / 2 : ℝ) ^ j ∧
      (∀ j' : ℕ, j = j' + 1 →
        dist (u (sphereSelIdx u V j)) (u (sphereSelIdx u V j'))
          < (1 / 2 : ℝ) ^ j' + (1 / 2 : ℝ) ^ j) := by
  have hne : V.sphere.Nonempty := V.nonempty_sphere
  intro j
  induction j with
  | zero =>
      obtain ⟨y, hy⟩ := hne
      obtain ⟨i, hi⟩ := Metric.mem_closure_iff.1 (hu.closure_eq ▸ Set.mem_univ y) 1 one_pos
      obtain ⟨i', rfl⟩ := hi.1
      have hmem : i' ∈ {i | infDist (u i) V.sphere < 1} := by
        refine lt_of_le_of_lt (infDist_le_dist_of_mem hy) ?_
        rw [dist_comm]
        exact hi.2
      have hS : {i | infDist (u i) V.sphere < 1}.Nonempty := ⟨i', hmem⟩
      refine ⟨?_, fun j' hj' => absurd hj' (by omega)⟩
      rw [pow_zero, sphereSelIdx_zero]
      exact Nat.sInf_mem hS
  | succ j ih =>
      obtain ⟨hj, -⟩ := ih
      obtain ⟨y, hyS, hy⟩ := (infDist_lt_iff hne).1 hj
      obtain ⟨i, hi⟩ := Metric.mem_closure_iff.1 (hu.closure_eq ▸ Set.mem_univ y)
        ((1 / 2 : ℝ) ^ (j + 1)) (by positivity)
      obtain ⟨i', rfl⟩ := hi.1
      have hd1 : infDist (u i') V.sphere < (1 / 2 : ℝ) ^ (j + 1) :=
        lt_of_le_of_lt (infDist_le_dist_of_mem hyS) (by rw [dist_comm]; exact hi.2)
      have hd2 : dist (u i') (u (sphereSelIdx u V j))
          < (1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ (j + 1) := by
        calc dist (u i') (u (sphereSelIdx u V j))
            ≤ dist (u i') y + dist y (u (sphereSelIdx u V j)) := dist_triangle _ _ _
          _ < (1 / 2 : ℝ) ^ (j + 1) + (1 / 2 : ℝ) ^ j := by
              refine add_lt_add ?_ ?_
              · rw [dist_comm]; exact hi.2
              · rw [dist_comm]; exact hy
          _ = (1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ (j + 1) := by ring
      have hS : {i | infDist (u i) V.sphere < (1 / 2 : ℝ) ^ (j + 1) ∧
          dist (u i) (u (sphereSelIdx u V j))
            < (1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ (j + 1)}.Nonempty := ⟨i', hd1, hd2⟩
      have hmem := Nat.sInf_mem hS
      rw [sphereSelIdx_succ]
      refine ⟨hmem.1, fun j' hj' => ?_⟩
      obtain rfl : j' = j := by omega
      exact hmem.2

theorem measurable_sphereSelIdx {k : ℕ} [NeZero k] {u : ℕ → X} (hu : DenseRange u) (j : ℕ) :
    Measurable fun V : GrassmannianFin X k => sphereSelIdx u V j := by
  induction j with
  | zero =>
      have hm : ∀ i, MeasurableSet {V : GrassmannianFin X k | infDist (u i) V.sphere < 1} :=
        fun i => measurableSet_lt (continuous_infDist_sphere k (u i)).measurable measurable_const
      have hne : ∀ V : GrassmannianFin X k, ∃ i, infDist (u i) V.sphere < 1 := by
        intro V
        obtain ⟨h, -⟩ := sphereSelIdx_spec hu V 0
        rw [pow_zero, sphereSelIdx_zero] at h
        exact ⟨sInf {i | infDist (u i) V.sphere < 1}, h⟩
      simp only [sphereSelIdx_zero]
      exact measurable_sInf_of_measurable (Ω := GrassmannianFin X k)
        (fun i V => infDist (u i) V.sphere < 1) hm hne
  | succ j ih =>
      have hm : ∀ i, MeasurableSet {V : GrassmannianFin X k |
          infDist (u i) V.sphere < (1 / 2 : ℝ) ^ (j + 1) ∧
          dist (u i) (u (sphereSelIdx u V j)) < (1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ (j + 1)} := by
        intro i
        rw [Set.ofPred_and]
        refine MeasurableSet.inter
          (measurableSet_lt (continuous_infDist_sphere k (u i)).measurable measurable_const) ?_
        have hpre : {V : GrassmannianFin X k | dist (u i) (u (sphereSelIdx u V j))
              < (1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ (j + 1)}
            = (fun V => sphereSelIdx u V j) ⁻¹'
              {l | dist (u i) (u l) < (1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ (j + 1)} := rfl
        rw [hpre]
        exact ih trivial
      have hne : ∀ V : GrassmannianFin X k, ∃ i,
          infDist (u i) V.sphere < (1 / 2 : ℝ) ^ (j + 1) ∧
          dist (u i) (u (sphereSelIdx u V j)) < (1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ (j + 1) := by
        intro V
        obtain ⟨h1, h2⟩ := sphereSelIdx_spec hu V (j + 1)
        exact ⟨sphereSelIdx u V (j + 1), h1, h2 j rfl⟩
      simp only [sphereSelIdx_succ]
      exact measurable_sInf_of_measurable (Ω := GrassmannianFin X k)
        (fun i V => infDist (u i) V.sphere < (1 / 2 : ℝ) ^ (j + 1) ∧
          dist (u i) (u (sphereSelIdx u V j)) < (1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ (j + 1)) hm hne

theorem sphereSelIdx_cauchySeq {k : ℕ} [NeZero k] {u : ℕ → X} (hu : DenseRange u)
    (V : GrassmannianFin X k) : CauchySeq fun j => u (sphereSelIdx u V j) := by
  refine cauchySeq_of_le_geometric (r := (1 / 2 : ℝ)) (C := 2) (by norm_num) ?_
  intro j
  have h := (sphereSelIdx_spec hu V (j + 1)).2 j rfl
  rw [dist_comm]
  refine h.le.trans ?_
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  have : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ j := by
    rw [pow_succ]
    linarith
  linarith

open scoped Classical in
/-- **A measurable unit vector inside each subspace.** This is the measurable-selection step the
retraction argument needs; it is genuine measurable selection, but a cheap case of it, because
`V ↦ 𝕊_V` is an *isometry* into the space of nonempty compacts. -/
noncomputable def sphereSel {k : ℕ} (u : ℕ → X)
    (V : GrassmannianFin X k) : X :=
  limUnder atTop fun j => u (sphereSelIdx u V j)

theorem sphereSel_tendsto {k : ℕ} [NeZero k] [CompleteSpace X] {u : ℕ → X} (hu : DenseRange u)
    (V : GrassmannianFin X k) :
    Tendsto (fun j => u (sphereSelIdx u V j)) atTop (nhds (sphereSel u V)) :=
  (sphereSelIdx_cauchySeq hu V).tendsto_limUnder

theorem sphereSel_mem {k : ℕ} [NeZero k] [CompleteSpace X] {u : ℕ → X} (hu : DenseRange u)
    (V : GrassmannianFin X k) : sphereSel u V ∈ V.sphere := by
  have hclosed : IsClosed V.sphere := V.isCompact_sphere.isClosed
  have hne : V.sphere.Nonempty := V.nonempty_sphere
  have hzero : infDist (sphereSel u V) V.sphere = 0 := by
    refine le_antisymm ?_ infDist_nonneg
    have hb : ∀ j : ℕ, infDist (sphereSel u V) V.sphere
        ≤ (1 / 2 : ℝ) ^ j + dist (sphereSel u V) (u (sphereSelIdx u V j)) := by
      intro j
      have h1 := infDist_le_infDist_add_dist (x := sphereSel u V)
        (y := u (sphereSelIdx u V j)) (s := V.sphere)
      have h2 := (sphereSelIdx_spec hu V j).1
      linarith
    have hlim : Tendsto (fun j : ℕ =>
        (1 / 2 : ℝ) ^ j + dist (sphereSel u V) (u (sphereSelIdx u V j))) atTop (nhds 0) := by
      have hA : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have hB : Tendsto (fun j : ℕ => dist (sphereSel u V) (u (sphereSelIdx u V j)))
          atTop (nhds 0) := by
        have hd := tendsto_iff_dist_tendsto_zero.1 (sphereSel_tendsto hu V)
        simpa [dist_comm] using hd
      simpa using hA.add hB
    exact ge_of_tendsto hlim (Eventually.of_forall hb)
  have hmem : sphereSel u V ∈ closure V.sphere := by
    rw [Metric.mem_closure_iff_infDist_zero hne]
    exact hzero
  rwa [hclosed.closure_eq] at hmem

theorem measurable_sphereSel {k : ℕ} [NeZero k] [CompleteSpace X] [MeasurableSpace X]
    [BorelSpace X] {u : ℕ → X} (hu : DenseRange u) :
    Measurable (sphereSel (k := k) u) := by
  refine measurable_of_tendsto_metrizable
    (f := fun j (V : GrassmannianFin X k) => u (sphereSelIdx u V j)) ?_ ?_
  · intro j
    exact measurable_from_nat.comp (measurable_sphereSelIdx hu j)
  · rw [tendsto_pi_nhds]
    exact fun V => sphereSel_tendsto hu V

/-- A countable family of continuous functionals separating the points of a separable space:
Hahn--Banach norming functionals at a dense sequence. -/
theorem exists_separating_dual_seq [SeparableSpace X] :
    ∃ f : ℕ → (X →L[ℝ] ℝ), ∀ x : X, x ≠ 0 → ∃ i, f i x ≠ 0 := by
  classical
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq X
  have hchoice : ∀ n : ℕ, ∃ g : X →L[ℝ] ℝ, ‖g‖ ≤ 1 ∧ g (u n) = ‖u n‖ := by
    intro n
    obtain ⟨g, hg1, hg2⟩ := exists_dual_vector'' (𝕜 := ℝ) (u n)
    exact ⟨g, hg1, by simpa using hg2⟩
  choose f hfnorm hfval using hchoice
  refine ⟨f, fun x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨n, hn⟩ := Metric.mem_closure_iff.1 (hu.closure_eq ▸ Set.mem_univ x)
    (‖x‖ / 3) (by positivity)
  obtain ⟨n', rfl⟩ := hn.1
  have hd : ‖x - u n'‖ < ‖x‖ / 3 := by
    rw [← dist_eq_norm]
    exact hn.2
  have hun : ‖x‖ - ‖x‖ / 3 < ‖u n'‖ := by
    have := norm_sub_norm_le x (u n')
    linarith
  refine ⟨n', ?_⟩
  have hkey : ‖x‖ / 3 < f n' x := by
    have hsplit : f n' x = f n' (u n') + f n' (x - u n') := by
      rw [← map_add]
      congr 1
      abel
    have hb : |f n' (x - u n')| ≤ ‖x - u n'‖ := by
      have := (f n').le_opNorm (x - u n')
      have h1 : ‖f n' (x - u n')‖ ≤ ‖f n'‖ * ‖x - u n'‖ := this
      have h2 : ‖f n'‖ * ‖x - u n'‖ ≤ 1 * ‖x - u n'‖ :=
        mul_le_mul_of_nonneg_right (hfnorm n') (norm_nonneg _)
      simpa [Real.norm_eq_abs] using h1.trans (by linarith)
    rw [hsplit, hfval n']
    have := abs_le.1 hb
    linarith
  intro h0
  rw [h0] at hkey
  linarith

/-- `x ↦ x - f(x)v` maps `V` onto the hyperplane `V ⊓ ker f`, when `v ∈ V` and `f v = 1`. -/
theorem map_sub_smulRight (f : X →L[ℝ] ℝ) (V : Submodule ℝ X) {v : X} (hv : v ∈ V)
    (hfv : f v = 1) :
    Submodule.map
        (((ContinuousLinearMap.id ℝ X - f.smulRight v : X →L[ℝ] X)) : X →ₗ[ℝ] X) V
      = V ⊓ LinearMap.ker (f : X →ₗ[ℝ] ℝ) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hval : ((ContinuousLinearMap.id ℝ X - f.smulRight v : X →L[ℝ] X)) x = x - f x • v := rfl
    refine ⟨?_, ?_⟩
    · change ((ContinuousLinearMap.id ℝ X - f.smulRight v : X →L[ℝ] X)) x ∈ V
      rw [hval]
      exact V.sub_mem hx (V.smul_mem _ hv)
    · change (f : X →ₗ[ℝ] ℝ) _ = 0
      change f (((ContinuousLinearMap.id ℝ X - f.smulRight v : X →L[ℝ] X)) x) = 0
      rw [hval, map_sub, map_smul, hfv]
      simp
  · rintro ⟨hzV, hzk⟩
    refine ⟨z, hzV, ?_⟩
    have hval : ((ContinuousLinearMap.id ℝ X - f.smulRight v : X →L[ℝ] X)) z = z - f z • v := rfl
    change ((ContinuousLinearMap.id ℝ X - f.smulRight v : X →L[ℝ] X)) z = z
    rw [hval, show f z = 0 from hzk]
    simp

/-- …and it drops the dimension by exactly one. -/
theorem finrank_map_sub_smulRight (f : X →L[ℝ] ℝ) (V : Submodule ℝ X)
    [FiniteDimensional ℝ V] {v : X} (hv : v ∈ V) (hfv : f v = 1) :
    finrank ℝ (Submodule.map
        (((ContinuousLinearMap.id ℝ X - f.smulRight v : X →L[ℝ] X)) : X →ₗ[ℝ] X) V) + 1
      = finrank ℝ V := by
  set P : X →L[ℝ] X := ContinuousLinearMap.id ℝ X - f.smulRight v with hP
  set g : V →ₗ[ℝ] X := (P : X →ₗ[ℝ] X).domRestrict V with hg
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, map_zero] at hfv
    exact one_ne_zero hfv.symm
  have hval : ∀ x : X, (P : X →ₗ[ℝ] X) x = x - f x • v := fun x => rfl
  have hrange : LinearMap.range g = Submodule.map ((P : X →ₗ[ℝ] X)) V :=
    LinearMap.range_domRestrict _ _
  have hker : LinearMap.ker g = Submodule.span ℝ {(⟨v, hv⟩ : V)} := by
    ext x
    simp only [hg, LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_span_singleton]
    constructor
    · intro hx
      refine ⟨f (x : X), ?_⟩
      apply Subtype.ext
      have hz : (x : X) - f (x : X) • v = 0 := by rw [← hval]; exact hx
      change f (x : X) • v = (x : X)
      exact (sub_eq_zero.1 hz).symm
    · rintro ⟨c, rfl⟩
      have hc : ((c • (⟨v, hv⟩ : V) : V) : X) = c • v := rfl
      rw [hc, hval, map_smul, hfv]
      simp
  have hne : (⟨v, hv⟩ : V) ≠ 0 := by
    intro h
    exact hv0 (congrArg Subtype.val h)
  have hfk : finrank ℝ (LinearMap.ker g) = 1 := by
    rw [hker]
    exact finrank_span_singleton hne
  have hsum := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange, hfk] at hsum
  exact hsum

/-- **The hyperplane cut, for one functional.** Given a measurable choice `e V ∈ V` and a
functional `f`, the family `V ↦ V ⊓ ker f` is measurable, and is a proper subspace of `V`
wherever `f(e V) ≠ 0`. -/
theorem exists_measurable_hyperplane [SeparableSpace X] [CompleteSpace X] [MeasurableSpace X]
    [BorelSpace X] (k : ℕ) [NeZero k] [Nonempty (GrassmannianFin X k)]
    (f : X →L[ℝ] ℝ) (e : GrassmannianFin X (k + 1) → X) (hem : Measurable e)
    (hemem : ∀ V, e V ∈ (V.1 : Submodule ℝ X)) :
    ∃ W : GrassmannianFin X (k + 1) → GrassmannianFin X k, Measurable W ∧
      ∀ V, f (e V) ≠ 0 → (W V).1 < V.1 ∧ e V ∉ (W V).1 := by
  classical
  obtain ⟨A, hA⟩ : ∃ A : GrassmannianFin X (k + 1) → (X →L[ℝ] X), ∀ V,
      A V = ContinuousLinearMap.id ℝ X - f.smulRight ((f (e V))⁻¹ • e V) :=
    ⟨_, fun V => rfl⟩
  obtain ⟨Wsub, hWsub⟩ : ∃ Wsub : GrassmannianFin X (k + 1) → Submodule ℝ X, ∀ V,
      Wsub V = if f (e V) = 0 then (Classical.arbitrary (GrassmannianFin X k)).1
        else Submodule.map ((A V : X →L[ℝ] X) : X →ₗ[ℝ] X) (V.1 : Submodule ℝ X) :=
    ⟨_, fun V => rfl⟩
  have hvmem : ∀ V, (f (e V))⁻¹ • e V ∈ (V.1 : Submodule ℝ X) :=
    fun V => (V.1 : Submodule ℝ X).smul_mem _ (hemem V)
  have hfv : ∀ V, f (e V) ≠ 0 → f ((f (e V))⁻¹ • e V) = 1 := by
    intro V h
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ h]
  have hWneg : ∀ V, f (e V) ≠ 0 →
      Wsub V = (V.1 : Submodule ℝ X) ⊓ LinearMap.ker (f : X →ₗ[ℝ] ℝ) := by
    intro V h
    rw [hWsub V, ite_eq_right h, hA V,
      map_sub_smulRight f (V.1 : Submodule ℝ X) (hvmem V) (hfv V h)]
  have hWprop : ∀ V, FiniteDimensional ℝ (Wsub V) ∧ finrank ℝ (Wsub V) = k := by
    intro V
    have hVfd : FiniteDimensional ℝ (V.1 : Submodule ℝ X) := V.2.1
    by_cases h : f (e V) = 0
    · rw [hWsub V, ite_eq_left h]
      exact (Classical.arbitrary (GrassmannianFin X k)).2
    · rw [hWsub V, ite_eq_right h, hA V]
      have hfd : FiniteDimensional ℝ
          (Submodule.map (((ContinuousLinearMap.id ℝ X
            - f.smulRight ((f (e V))⁻¹ • e V) : X →L[ℝ] X)) : X →ₗ[ℝ] X)
            (V.1 : Submodule ℝ X)) := by
        have hfg : ((V.1 : Submodule ℝ X)).FG := (Submodule.fg_iff_finiteDimensional _).2 hVfd
        exact (Submodule.fg_iff_finiteDimensional _).1 (hfg.map _)
      refine ⟨hfd, ?_⟩
      have hrk := finrank_map_sub_smulRight f (V.1 : Submodule ℝ X) (hvmem V) (hfv V h)
      rw [V.2.2] at hrk
      omega
  refine ⟨fun V => ⟨Wsub V, hWprop V⟩, ?_, ?_⟩
  · refine measurable_of_measurable_infDist k fun x => ?_
    change Measurable fun V => infDist x ((Wsub V : Submodule ℝ X) : Set X)
    have hsplit : (fun V => infDist x ((Wsub V : Submodule ℝ X) : Set X))
        = Set.piecewise {V | f (e V) = 0}
            (fun _ => infDist x (((Classical.arbitrary (GrassmannianFin X k)).1
              : Submodule ℝ X) : Set X))
            (fun V => infDist x (((A V) '' (((V.1 : Submodule ℝ X)) : Set X)))) := by
      funext V
      by_cases h : f (e V) = 0
      · have hmem : V ∈ {V : GrassmannianFin X (k + 1) | f (e V) = 0} := h
        rw [Set.piecewise_eq_of_mem _ _ _ hmem, hWsub V, ite_eq_left h]
      · have hmem : V ∉ {V : GrassmannianFin X (k + 1) | f (e V) = 0} := h
        rw [Set.piecewise_eq_of_notMem _ _ _ hmem, hWsub V, ite_eq_right h]
        congr 1
    rw [hsplit]
    have hcond : MeasurableSet {V : GrassmannianFin X (k + 1) | f (e V) = 0} :=
      measurableSet_eq_fun (f.continuous.measurable.comp hem) measurable_const
    refine Measurable.piecewise hcond measurable_const ?_
    refine measurable_infDist_map (k + 1) measurable_id ?_ x
    intro y
    have hval : (fun V : GrassmannianFin X (k + 1) => A V y)
        = fun V => y - f y • ((f (e V))⁻¹ • e V) := by
      funext V
      rw [hA V]
      rfl
    rw [hval]
    exact measurable_const.sub (((f.continuous.measurable.comp hem).inv.smul hem).const_smul _)
  · intro V h
    refine ⟨?_, ?_⟩
    · change Wsub V < (V.1 : Submodule ℝ X)
      have hlt : Wsub V ≤ (V.1 : Submodule ℝ X) := by
        rw [hWneg V h]
        exact inf_le_left
      refine lt_of_le_of_ne hlt ?_
      intro heq
      have h1 := (hWprop V).2
      rw [heq, V.2.2] at h1
      omega
    · change e V ∉ Wsub V
      rw [hWneg V h]
      intro hmem
      exact h hmem.2

end SphereSelection

/-- Every finite-dimensional subspace `K` contains a subspace of any prescribed dimension
`l ≤ finrank K`: take the span of the first `l` vectors of a basis of `K`. Mathlib has no
ready-made form of this, so it is proved here; it is what supplies the `l`-dimensional witness
`W ≤ U ⊓ V` needed by `Tsmallgrow`. -/
theorem exists_le_finrank_eq' {M : Type*} [AddCommGroup M] [Module ℝ M]
    (K : Submodule ℝ M) [FiniteDimensional ℝ K] {l : ℕ} (hl : l ≤ Module.finrank ℝ K) :
    ∃ W : Submodule ℝ M, W ≤ K ∧ FiniteDimensional ℝ W ∧ Module.finrank ℝ W = l := by
  classical
  have hind : LinearIndependent ℝ
      (fun i : Fin l => ((Module.finBasis ℝ K) (Fin.castLE hl i) : M)) := by
    have h1 : LinearIndependent ℝ (fun i : Fin l => (Module.finBasis ℝ K) (Fin.castLE hl i)) :=
      (Module.finBasis ℝ K).linearIndependent.comp _ (Fin.castLE_injective hl)
    exact h1.map' K.subtype K.ker_subtype
  have hle : Submodule.span ℝ
      (Set.range fun i : Fin l => ((Module.finBasis ℝ K) (Fin.castLE hl i) : M)) ≤ K := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ((Module.finBasis ℝ K) (Fin.castLE hl i)).2
  refine ⟨_, hle, Submodule.finiteDimensional_of_le hle, ?_⟩
  rw [finrank_span_eq_card hind, Fintype.card_fin]


open Module in
/-- **Retraction together with its complementary unit vector.**
The measurable selection produces both at once:
the selected unit vector `e V ∈ 𝕊_V` is the
one the functional does not kill, so it spans a complement of `U V = V ⊓ ker f` inside `V`.

Stated jointly because the complement is not produced from an *arbitrary* measurable retraction
— it comes from this one. -/
theorem exists_measurable_retract_complement [SeparableSpace X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X] (k : ℕ) [NeZero k] :
    ∃ (U : GrassmannianFin X (k + 1) → GrassmannianFin X k) (b : GrassmannianFin X (k + 1) → X),
      Measurable U ∧ Measurable b ∧
      ∀ V, ‖b V‖ = 1 ∧ (U V).1 ⊔ Submodule.span ℝ {b V} = V.1 := by
  classical
  rcases isEmpty_or_nonempty (GrassmannianFin X (k + 1)) with hE | hNE
  · exact ⟨fun V => (IsEmpty.false V).elim, fun V => (IsEmpty.false V).elim,
      Subsingleton.measurable, Subsingleton.measurable, fun V => (IsEmpty.false V).elim⟩
  · have : Nonempty (GrassmannianFin X k) := by
      obtain ⟨V⟩ := hNE
      have : FiniteDimensional ℝ (V.1 : Submodule ℝ X) := V.2.1
      obtain ⟨W, -, hWfd, hWrank⟩ := exists_le_finrank_eq' (V.1 : Submodule ℝ X)
        (l := k) (by rw [V.2.2]; omega)
      exact ⟨⟨W, hWfd, hWrank⟩⟩
    obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq X
    obtain ⟨f, hfsep⟩ := exists_separating_dual_seq (X := X)
    have hem : Measurable (sphereSel (k := k + 1) u) := measurable_sphereSel hu
    have hesph : ∀ V : GrassmannianFin X (k + 1), sphereSel u V ∈ V.sphere :=
      fun V => sphereSel_mem hu V
    have henorm : ∀ V : GrassmannianFin X (k + 1), ‖sphereSel u V‖ = 1 :=
      fun V => mem_sphere_zero_iff_norm.1 (hesph V).1
    have hemem : ∀ V : GrassmannianFin X (k + 1),
        sphereSel u V ∈ (V.1 : Submodule ℝ X) := fun V => (hesph V).2
    have hene : ∀ V : GrassmannianFin X (k + 1), sphereSel u V ≠ 0 := by
      intro V h
      have hn := henorm V
      rw [h, norm_zero] at hn
      exact zero_ne_one hn
    choose W hWm hWlt using fun i =>
      exists_measurable_hyperplane k (f i) (sphereSel u) hem hemem
    have hSmeas : ∀ i, MeasurableSet {V : GrassmannianFin X (k + 1) | f i (sphereSel u V) ≠ 0} :=
      fun i => (measurableSet_eq_fun ((f i).continuous.measurable.comp hem)
        measurable_const).compl
    have hcover : (⋃ i, {V : GrassmannianFin X (k + 1) | f i (sphereSel u V) ≠ 0})
        = Set.univ := by
      ext V
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true, Set.mem_ofPred_eq]
      exact hfsep (sphereSel u V) (hene V)
    obtain ⟨N, hN, -, hNspec⟩ := measurable_of_countable_cover (Y := ℕ) id
      (fun i => {V : GrassmannianFin X (k + 1) | f i (sphereSel u V) ≠ 0}) hSmeas hcover
    refine ⟨fun V => W (N V) V, sphereSel u, measurable_glue hN hWm, hem, fun V => ⟨henorm V, ?_⟩⟩
    obtain ⟨hlt, hnot⟩ := hWlt (N V) V (hNspec V).1
    set W₀ : Submodule ℝ X := (W (N V) V).1 with hW₀
    have hVfd : FiniteDimensional ℝ (V.1 : Submodule ℝ X) := V.2.1
    have hW₀fd : FiniteDimensional ℝ W₀ := (W (N V) V).2.1
    -- the sum sits inside `V`
    have hle : W₀ ⊔ Submodule.span ℝ {sphereSel u V} ≤ (V.1 : Submodule ℝ X) :=
      sup_le hlt.le (Submodule.span_le.2 (by simpa using hemem V))
    -- and has the right dimension
    have hinf : W₀ ⊓ Submodule.span ℝ {sphereSel u V} = ⊥ := by
      refine le_antisymm ?_ bot_le
      rintro x ⟨hxW, hxs⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hxs
      rcases eq_or_ne c 0 with rfl | hc
      · simp
      · exact absurd (by simpa [Submodule.smul_mem_iff, hc] using hxW) hnot
    have hspan : finrank ℝ (Submodule.span ℝ {sphereSel u V}) = 1 :=
      finrank_span_singleton (hene V)
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq W₀ (Submodule.span ℝ {sphereSel u V})
    rw [hinf, finrank_bot, hspan, (W (N V) V).2.2] at hsum
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [V.2.2]
    omega

/-- A measurable strict-subspace retraction for the canonical Grassmannian Borel structures.
It follows from the joint selection of a hyperplane and its complementary unit vector. -/
theorem exists_measurable_retract [SeparableSpace X] [CompleteSpace X] [MeasurableSpace X]
    [BorelSpace X] (k : ℕ) [NeZero k] :
    ∃ U : GrassmannianFin X (k + 1) → GrassmannianFin X k, Measurable U ∧
      ∀ V, (U V).1 < V.1 := by
  obtain ⟨U, b, hU, -, hUb⟩ := exists_measurable_retract_complement (X := X) k
  refine ⟨U, hU, fun V => lt_of_le_of_ne ?_ ?_⟩
  · exact le_trans le_sup_left (hUb V).2.le
  · intro heq
    have hrank := congrArg (fun W : Submodule ℝ X => Module.finrank ℝ W) heq
    rw [(U V).2.2, V.2.2] at hrank
    omega

section RetractCounterexample

open Module _root_.Submodule MultiplicativeErgodic.Submodule


/-- Three-dimensional Euclidean space for the retraction counterexample. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The orthogonal complement of a nonzero `v` is a 2-dimensional subspace of `E3` not
containing `v`. -/
noncomputable def planeMissing (v : E3) (hv : v ≠ 0) : GrassmannianFin E3 2 := by
  refine ⟨(ℝ ∙ v)ᗮ, FiniteDimensional.finiteDimensional_submodule _, ?_⟩
  have h1 : finrank ℝ (ℝ ∙ v) = 1 := finrank_span_singleton hv
  have h2 := Submodule.finrank_add_finrank_orthogonal (K := (ℝ ∙ v)) (E := E3)
  have h3 : finrank ℝ E3 = 3 := by simp
  omega

theorem v_notMem_planeMissing (v : E3) (hv : v ≠ 0) : v ∉ ((ℝ ∙ v)ᗮ : Submodule ℝ E3) := by
  intro hmem
  have := hmem v (Submodule.mem_span_singleton_self v)
  rw [real_inner_self_eq_norm_sq] at this
  exact hv (norm_eq_zero.mp (by nlinarith [norm_nonneg v]))

/-- **Why `exists_measurable_retract` must use the canonical Borel σ-algebra.** With the
σ-algebras taken as hypotheses — as they were until this was found — the statement is universally
quantified over them and is false: give the source the indiscrete σ-algebra and the target the
discrete one, and `Measurable U` forces `U` constant, while no single line lies inside every plane
of `ℝ³`. Kept as a regression test against reintroducing the binders. -/
theorem exists_measurable_retract_false :
    ¬ ∀ (k : ℕ) [MeasurableSpace (GrassmannianFin E3 (k + 1))]
        [MeasurableSpace (GrassmannianFin E3 k)],
      ∃ U : GrassmannianFin E3 (k + 1) → GrassmannianFin E3 k, Measurable U ∧
        ∀ V, (U V).1 < V.1 := by
  intro h
  obtain ⟨U, hmeas, hlt⟩ := @h 1 ⊥ ⊤
  have hconst : ∀ V W : GrassmannianFin E3 2, U V = U W := by
    intro V W
    have hs : @MeasurableSet _ ⊥ (U ⁻¹' {U V}) := hmeas (by trivial)
    rw [MeasurableSpace.measurableSet_bot_iff] at hs
    rcases hs with h1 | h1
    · exact absurd (show V ∈ U ⁻¹' {U V} from rfl) (by rw [h1]; exact id)
    · have hW : W ∈ U ⁻¹' {U V} := by rw [h1]; trivial
      exact (Set.mem_singleton_iff.mp hW).symm
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : E3)
  set V₀ : GrassmannianFin E3 2 := planeMissing v₀ hv₀ with hV₀
  have hLdim : finrank ℝ (U V₀).1 = 1 := (U V₀).2.2
  have hLne : (U V₀).1 ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hLdim
    exact one_ne_zero hLdim.symm
  obtain ⟨v, hvL, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLne
  have hlt' := hlt (planeMissing v hv0)
  rw [hconst (planeMissing v hv0) V₀] at hlt'
  exact v_notMem_planeMissing v hv0 (le_of_lt hlt' hvL)

end RetractCounterexample


open Module in
/-- The measurable basis, built by induction from dimension `1` upward: at each step the
retraction `U` peels off a hyperplane and `b` supplies the missing direction. Stated at `k+1` so
that no `NeZero` instance is needed for the induction to typecheck (`𝒢_0X` carries no metric
here). -/
theorem measbase_aux [SeparableSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (k : ℕ) :
    ∃ b : GrassmannianFin X (k + 1) → Fin (k + 1) → X,
      Measurable b ∧ ∀ V, (V.1 : Submodule ℝ X) = Submodule.span ℝ (Set.range (b V)) := by
  classical
  induction k with
  | zero =>
      obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq X
      refine ⟨fun V _ => sphereSel u V, measurable_pi_iff.mpr fun _ => measurable_sphereSel hu,
        fun V => ?_⟩
      have hmem : sphereSel u V ∈ (V.1 : Submodule ℝ X) := (sphereSel_mem hu V).2
      have hne : sphereSel u V ≠ 0 := by
        intro h
        have hn := mem_sphere_zero_iff_norm.1 (sphereSel_mem hu V).1
        rw [h, norm_zero] at hn
        exact zero_ne_one hn
      have : FiniteDimensional ℝ (V.1 : Submodule ℝ X) := V.2.1
      have hrange : Set.range (fun _ : Fin 1 => sphereSel u V) = {sphereSel u V} := by
        ext z; simp
      rw [hrange]
      refine (Submodule.eq_of_le_of_finrank_eq
        (Submodule.span_le.2 (by simpa using hmem)) ?_).symm
      rw [finrank_span_singleton hne, V.2.2]
  | succ k ih =>
      obtain ⟨U, c, hUm, hcm, hspec⟩ := exists_measurable_retract_complement (X := X) (k + 1)
      obtain ⟨bk, hbkm, hbk⟩ := ih
      refine ⟨fun V => Fin.snoc (bk (U V)) (c V), ?_, fun V => ?_⟩
      · refine measurable_pi_iff.mpr fun i => ?_
        induction i using Fin.lastCases with
        | last => simpa using hcm
        | cast i =>
            simp only [Fin.snoc_castSucc]
            exact ((measurable_pi_apply i).comp hbkm).comp hUm
      · have hrange : Set.range (Fin.snoc (bk (U V)) (c V) : Fin (k + 2) → X)
            = insert (c V) (Set.range (bk (U V))) := by
          ext z
          simp only [Set.mem_range, Set.mem_insert_iff]
          constructor
          · rintro ⟨i, rfl⟩
            induction i using Fin.lastCases with
            | last => exact Or.inl (by simp)
            | cast i => exact Or.inr ⟨i, by simp⟩
          · rintro (rfl | ⟨i, rfl⟩)
            · exact ⟨Fin.last (k + 1), by simp⟩
            · exact ⟨i.castSucc, by simp⟩
        rw [hrange, Submodule.span_insert, ← hbk (U V), sup_comm]
        exact (hspec V).2.symm

open Module in
/-- **Lemma \ref{measbase}.** For a separable Banach space `X` and every `k ≥ 1`, there is a
measurable choice of basis `b : 𝒢_kX → 𝕊_X^k`.

**Hypotheses added:** `[CompleteSpace X]`, inherited from `exists_measurable_retract`. -/
theorem measbase [SeparableSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (k : ℕ) [NeZero k] :
    ∃ b : GrassmannianFin X k → Fin k → X,
      Measurable b ∧ ∀ V, (V.1 : Submodule ℝ X) = Submodule.span ℝ (Set.range (b V)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := NeZero.ne k; omega⟩
  exact measbase_aux j

/-- `growth` is antitone in the subspace: shrinking the subspace shrinks the unit sphere over
which the infimum is taken, so the infimum can only go up. This is the paper's step
`g_T(U) ≤ g_T(U ∩ V)`. The nonemptiness hypothesis on the smaller sphere is not decorative:
`sInf ∅ = 0` in `ℝ`, so without it the statement fails for `W = ⊥`. -/
theorem growth_anti {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X →L[ℝ] Y) {W U : Submodule ℝ X} (hWU : W ≤ U)
    (hne : (Metric.sphere (0 : X) 1 ∩ (W : Set X)).Nonempty) :
    growth T U ≤ growth T W := by
  refine csInf_le_csInf ⟨0, ?_⟩ (hne.image _)
    (Set.image_mono (Set.inter_subset_inter (le_refl _) (SetLike.coe_subset_coe.2 hWU)))
  rintro _ ⟨z, -, rfl⟩
  exact norm_nonneg _

/-- On a subspace `W` of `V`, where the projection `P` acts as the identity, `T ∘ P` and `T`
have the same growth factor -- the paper's `g_{T∘Π}(U) = g_{T|_V}(U)` for `U ∈ 𝒢_l V`. -/
theorem growth_comp_of_le (T P : X →L[ℝ] X) {V W : Submodule ℝ X} (hWV : W ≤ V)
    (hidem : ∀ x ∈ V, P x = x) : growth (T.comp P) W = growth T W := by
  change sInf _ = sInf _
  congr 1
  refine Set.image_congr ?_
  intro x hx
  rw [ContinuousLinearMap.comp_apply, hidem x (hWV hx.2)]

/-- **Lemma \ref{Tsmallgrow}.** If `V` has finite codimension `k` and the bounded operator
`P : X → X` fixes `V`, then `ρ_{k+l}(T) ≤ ρ_l(T ∘ P)`.

**Statement change (working-practice note 4): `l ≠ 0` had to be added.** The paper's proof reads
`ρ_{k+l}(T) = sup_{U ∈ 𝒢_{k+l}X} g_T(U) ≤ sup_U g_T(U ∩ V) = sup_{U ∈ 𝒢_l V} g_{T∘Π}(U) ≤
ρ_l(T∘Π)`, and every step of that is formalized below. But at `l = 0` the Lean statement is
**false**, purely because of junk values: `𝒢_0X = {⊥}`, whose unit sphere is empty, so
`growth _ ⊥ = sInf ∅ = 0` and hence `ρ_0(S) = 0` for every `S`, whereas the paper's convention
makes `g` on the zero subspace an infimum over an empty sphere, i.e. `+∞`. Concretely, with
`X = ℝ`, `V = ⊥` (codimension `1`), `P = 0`, `T = id`, `k = 1`, `l = 0`, the hypotheses all hold
while `ρ_1(id) = 1 > 0 = ρ_0(id ∘ 0)`. The intended (and only true) reading needs `l ≥ 1`, which
is what every downstream call site in Section 5 supplies.

Only the identity of `P` on `V` is needed in this direction. A range condition is needed
by `Tbiggrow`, the converse inequality.

The mathematical core is the dimension count: a `(k+l)`-dimensional `U` meets the
codimension-`k` subspace `V` in dimension at least `l`, via rank-nullity for the composite
`U ↪ X ↠ X ⧸ V`. `exists_le_finrank_eq'` then extracts an honestly `l`-dimensional
`W ≤ U ⊓ V` to feed to the supremum defining `ρ_l`. -/
theorem Tsmallgrow (k l : ℕ) (hl : l ≠ 0) (V : GrassmannianCofin X k) (P : X →L[ℝ] X)
    (hidem : ∀ x ∈ (V.1.1 : Submodule ℝ X), P x = x)
    (T : X →L[ℝ] X) :
    bernsteinNumber T (k + l) ≤ bernsteinNumber (T.comp P) l := by
  have : NeZero l := ⟨hl⟩
  have : FiniteDimensional ℝ (X ⧸ (V.1.1 : Submodule ℝ X)) := V.2.1
  change sSup (Set.range fun U : GrassmannianFin X (k + l) => growth T (U.1 : Submodule ℝ X)) ≤ _
  refine Real.sSup_le ?_ (bernsteinNumber_nonneg _ _)
  rintro _ ⟨U, rfl⟩
  have : FiniteDimensional ℝ (U.1 : Submodule ℝ X) := U.2.1
  change growth T (U.1 : Submodule ℝ X) ≤ bernsteinNumber (T.comp P) l
  -- `f : U → X ⧸ V`; its kernel is `U ∩ V`, of dimension at least `l`
  have hker : LinearMap.ker
        ((V.1.1 : Submodule ℝ X).mkQ.comp (U.1 : Submodule ℝ X).subtype) =
      (V.1.1 : Submodule ℝ X).comap (U.1 : Submodule ℝ X).subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrk : Module.finrank ℝ (LinearMap.range
        ((V.1.1 : Submodule ℝ X).mkQ.comp (U.1 : Submodule ℝ X).subtype)) +
      Module.finrank ℝ (LinearMap.ker
        ((V.1.1 : Submodule ℝ X).mkQ.comp (U.1 : Submodule ℝ X).subtype)) = k + l := by
    rw [LinearMap.finrank_range_add_finrank_ker, U.2.2]
  have hrange_le : Module.finrank ℝ (LinearMap.range
      ((V.1.1 : Submodule ℝ X).mkQ.comp (U.1 : Submodule ℝ X).subtype)) ≤ k := by
    have h := Submodule.finrank_le (LinearMap.range
      ((V.1.1 : Submodule ℝ X).mkQ.comp (U.1 : Submodule ℝ X).subtype))
    rwa [V.2.2] at h
  -- transport the kernel back into `X`
  have hKU : ((V.1.1 : Submodule ℝ X).comap (U.1 : Submodule ℝ X).subtype).map
      (U.1 : Submodule ℝ X).subtype ≤ (U.1 : Submodule ℝ X) := Submodule.map_subtype_le _ _
  have hKV : ((V.1.1 : Submodule ℝ X).comap (U.1 : Submodule ℝ X).subtype).map
      (U.1 : Submodule ℝ X).subtype ≤ (V.1.1 : Submodule ℝ X) := Submodule.map_comap_le _ _
  have : FiniteDimensional ℝ (((V.1.1 : Submodule ℝ X).comap (U.1 : Submodule ℝ X).subtype).map
      (U.1 : Submodule ℝ X).subtype) := Submodule.finiteDimensional_of_le hKU
  have hKrank : Module.finrank ℝ
      (((V.1.1 : Submodule ℝ X).comap (U.1 : Submodule ℝ X).subtype).map
        (U.1 : Submodule ℝ X).subtype) =
      Module.finrank ℝ ((V.1.1 : Submodule ℝ X).comap (U.1 : Submodule ℝ X).subtype) :=
    Submodule.finrank_map_subtype_eq _ _
  rw [hker] at hrk
  have hlK : l ≤ Module.finrank ℝ
      (((V.1.1 : Submodule ℝ X).comap (U.1 : Submodule ℝ X).subtype).map
        (U.1 : Submodule ℝ X).subtype) := by omega
  obtain ⟨W, hWK, hWfin, hWrank⟩ := exists_le_finrank_eq' _ hlK
  have hne : (Metric.sphere (0 : X) 1 ∩ (W : Set X)).Nonempty :=
    GrassmannianFin.nonempty_sphere (⟨W, hWfin, hWrank⟩ : GrassmannianFin X l)
  calc growth T (U.1 : Submodule ℝ X)
      ≤ growth T W := growth_anti T (hWK.trans hKU) hne
    _ = growth (T.comp P) W := (growth_comp_of_le T P (hWK.trans hKV) hidem).symm
    _ ≤ bernsteinNumber (T.comp P) l :=
        le_csSup ⟨‖T.comp P‖, by rintro _ ⟨V', rfl⟩; exact growth_le_opNorm _ _⟩
          ⟨(⟨W, hWfin, hWrank⟩ : GrassmannianFin X l), rfl⟩


/-- A complement of a codimension-`k` subspace has dimension `k`. -/
theorem finrank_eq_of_isCompl_quotient {V E : Submodule ℝ X} (h : IsCompl V E)
     :
    Module.finrank ℝ E = Module.finrank ℝ (X ⧸ V) :=
  (LinearEquiv.finrank_eq (Submodule.quotientEquivOfIsCompl V E h)).symm

/-- `U ⊕ E` has dimension `l + k` when `U ≤ V` is `l`-dimensional and `E` is a complement of the
codimension-`k` subspace `V`. -/
theorem finrank_sup_of_isCompl {V E U : Submodule ℝ X} (h : IsCompl V E) (hUV : U ≤ V)
    [FiniteDimensional ℝ U] [FiniteDimensional ℝ E] :
    Module.finrank ℝ (U ⊔ E : Submodule ℝ X) = Module.finrank ℝ U + Module.finrank ℝ E := by
  have hinf : U ⊓ E = ⊥ := by
    refine le_antisymm ?_ bot_le
    calc U ⊓ E ≤ V ⊓ E := inf_le_inf_right _ hUV
      _ = ⊥ := h.inf_eq_bot
  have := Submodule.finrank_sup_add_finrank_inf_eq U E
  rw [hinf, finrank_bot] at this
  omega

/-- The pointwise estimate at the heart of `Tbiggrow`: on the unit sphere of `U ⊕ E`, where `U`
sits inside the slow space `V` and `E` is the fast space, `T` expands by at least
`g_T(U)/(4‖P'‖)`. -/
theorem Tbiggrow_pointwise {V E U : Submodule ℝ X} {P P' T : X →L[ℝ] X}
    (hPid : ∀ y ∈ V, P y = y) (hPzero : ∀ y ∈ E, P y = 0)
    (hcompat : ∀ y, P' (T y) = T (P y))
    (hUV : U ≤ V) (hUE : growth T U ≤ growth T E)
    (hP'norm : 1 ≤ ‖P'‖)
    {x : X} (hx : x ∈ U ⊔ E) (hxnorm : ‖x‖ = 1) :
    growth T U / (4 * ‖P'‖) ≤ ‖T x‖ := by
  obtain ⟨u, hu, e, he, rfl⟩ := Submodule.mem_sup.mp hx
  have hPx : P (u + e) = u := by
    rw [map_add, hPid u (hUV hu), hPzero e he, add_zero]
  have hTu : growth T U * ‖u‖ ≤ ‖T u‖ := growth_mul_norm_le T hu
  have hTe : growth T E * ‖e‖ ≤ ‖T e‖ := growth_mul_norm_le T he
  have hgU : 0 ≤ growth T U := growth_nonneg T U
  have hppos : (0:ℝ) < ‖P'‖ := lt_of_lt_of_le one_pos hP'norm
  -- the `V'`-component of `T x` is `T u`
  have h1 : ‖T u‖ ≤ ‖P'‖ * ‖T (u + e)‖ := by
    have : T u = P' (T (u + e)) := by rw [hcompat, hPx]
    rw [this]
    exact P'.le_opNorm _
  -- the complementary component is `T e`
  have h2 : ‖T e‖ ≤ (1 + ‖P'‖) * ‖T (u + e)‖ := by
    have hTe' : T e = T (u + e) - P' (T (u + e)) := by
      rw [hcompat, hPx, ← map_sub]
      congr 1
      abel
    calc ‖T e‖ = ‖T (u + e) - P' (T (u + e))‖ := by rw [hTe']
      _ ≤ ‖T (u + e)‖ + ‖P' (T (u + e))‖ := norm_sub_le _ _
      _ ≤ ‖T (u + e)‖ + ‖P'‖ * ‖T (u + e)‖ := by
          gcongr; exact P'.le_opNorm _
      _ = (1 + ‖P'‖) * ‖T (u + e)‖ := by ring
  have hsplit : 1 ≤ ‖u‖ + ‖e‖ := by
    calc (1:ℝ) = ‖u + e‖ := hxnorm.symm
      _ ≤ ‖u‖ + ‖e‖ := norm_add_le _ _
  have hTeU : growth T U * ‖e‖ ≤ ‖T e‖ :=
    le_trans (mul_le_mul_of_nonneg_right hUE (norm_nonneg e)) hTe
  rw [div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg u, norm_nonneg e, norm_nonneg (T (u + e))]

/-- Pushing an `l`-dimensional subspace forward by the projection `P` lands inside `V` and loses
at most a factor `‖P‖` of growth -- the paper's `ρ_l(T∘Π) ≤ ‖Π‖ρ_l(T|_V)`, in the pointwise form
that avoids naming `ρ_l(T|_V)`. -/
theorem exists_growth_ge_of_comp {V : Submodule ℝ X} {P T : X →L[ℝ] X}
    (hPmem : ∀ x, P x ∈ V) {l : ℕ} (U₀ : Submodule ℝ X) [FiniteDimensional ℝ U₀]
    (hU₀ : Module.finrank ℝ U₀ = l) (hpos : 0 < growth (T.comp P) U₀) :
    ∃ U : Submodule ℝ X, U ≤ V ∧ FiniteDimensional ℝ U ∧ Module.finrank ℝ U = l ∧
      growth (T.comp P) U₀ / ‖P‖ ≤ growth T U := by
  have hinjTP : Function.Injective ((T.comp P).toLinearMap.domRestrict U₀) :=
    injective_domRestrict_of_growth_pos hpos
  have hinjP : Function.Injective (P.toLinearMap.domRestrict U₀) := by
    intro a c hac
    refine hinjTP ?_
    change (T.comp P) (a : X) = (T.comp P) (c : X)
    have : P (a : X) = P (c : X) := hac
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, this]
  have hPne : P ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp only [ContinuousLinearMap.comp_zero] at hpos
    exact absurd (growth_eq_zero_of_forall_eq_zero (fun x _ => rfl)) (ne_of_gt hpos)
  have hPpos : 0 < ‖P‖ := norm_pos_iff.mpr hPne
  refine ⟨Submodule.map (P : X →ₗ[ℝ] X) U₀, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩; exact hPmem x
  · have he : U₀ ≃ₗ[ℝ] Submodule.map (P : X →ₗ[ℝ] X) U₀ :=
      (LinearEquiv.ofInjective _ hinjP).trans
        (LinearEquiv.ofEq _ _ (LinearMap.range_domRestrict _ _))
    exact Module.Finite.equiv he
  · have he : U₀ ≃ₗ[ℝ] Submodule.map (P : X →ₗ[ℝ] X) U₀ :=
      (LinearEquiv.ofInjective _ hinjP).trans
        (LinearEquiv.ofEq _ _ (LinearMap.range_domRestrict _ _))
    rw [← he.finrank_eq, hU₀]
  · -- every unit vector of `P U₀` is `P x` with `‖x‖ ≥ 1/‖P‖`
    refine le_csInf ?_ ?_
    · obtain ⟨y, hy⟩ : ∃ y : X, y ∈ Metric.sphere (0 : X) 1 ∩
          ((Submodule.map (P : X →ₗ[ℝ] X) U₀ : Submodule ℝ X) : Set X) := by
        by_contra hempty
        rw [not_exists] at hempty
        have : growth (T.comp P) U₀ ≤ 0 := by
          refine le_of_eq (growth_eq_zero_of_forall_eq_zero fun x hx => ?_)
          by_contra hne
          have hPx : P x ≠ 0 := by
            intro h
            exact hne (by rw [ContinuousLinearMap.comp_apply, h, map_zero])
          have hnpos : 0 < ‖P x‖ := norm_pos_iff.mpr hPx
          exact hempty (‖P x‖⁻¹ • P x)
            ⟨by rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
                  inv_mul_cancel₀ (ne_of_gt hnpos)],
             Submodule.smul_mem _ _ ⟨x, hx, rfl⟩⟩
        linarith
      exact ⟨‖T y‖, ⟨y, hy, rfl⟩⟩
    · rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
      obtain ⟨x, hxU, rfl⟩ := hy2
      rw [mem_sphere_zero_iff_norm] at hy1
      have hx : growth (T.comp P) U₀ * ‖x‖ ≤ ‖(T.comp P) x‖ := growth_mul_norm_le _ hxU
      have hxnorm : 1 ≤ ‖P‖ * ‖x‖ := by
        calc (1:ℝ) = ‖(P : X →ₗ[ℝ] X) x‖ := hy1.symm
          _ ≤ ‖P‖ * ‖x‖ := P.le_opNorm x
      rw [div_le_iff₀ hPpos]
      have hTP : ‖(T.comp P) x‖ = ‖T ((P : X →ₗ[ℝ] X) x)‖ := rfl
      rw [hTP] at hx
      nlinarith [growth_nonneg (T.comp P) U₀, norm_nonneg x]

/-- A nonzero idempotent operator has norm at least one. -/
theorem one_le_norm_of_isIdempotent {P : X →L[ℝ] X} (hidem : P.comp P = P) (hP : P ≠ 0) :
    1 ≤ ‖P‖ := by
  have hpos : 0 < ‖P‖ := norm_pos_iff.mpr hP
  have hle : ‖P‖ ≤ ‖P‖ * ‖P‖ := by
    calc ‖P‖ = ‖P.comp P‖ := by rw [hidem]
      _ ≤ ‖P‖ * ‖P‖ := P.opNorm_comp_le P
  nlinarith

/-- **Lemma \ref{Tbiggrow}.** Under a compatible pair of splittings `X = E ⊕ V = E' ⊕ V'`
with `P' ∘ T = T ∘ P` and `g_T(E) > ‖T|_V‖`, we get `ρ_l(T∘P) ≤ 4‖P‖‖P'‖ρ_{l+k}(T)`.

**Hypothesis-satisfiability note** (working-practice note 4). `hfast` must be stated with the
*restricted* norm `‖T|_V‖`, exactly as the paper does (`proof_met.tex` line 354), and **not** with
the ambient `‖T‖`: `growth_le_opNorm` gives `growth T E ≤ ‖T‖` for every `E`, so the variant
`growth T E > ‖T‖` is jointly unsatisfiable with it. That version made this theorem vacuously
true — provable in one line from the contradiction, and impossible for the Section 5 caller to
discharge. The intended reading is the genuine spectral-gap condition: the fast space `E` grows
strictly faster than `T` restricted to the slow space `V`, which is exactly `λ₁ > λ₂`.

**Statement repaired.** Two earlier versions were false. The first was vacuous
(`growth T E > ‖T‖` contradicts `growth_le_opNorm`); the second left `k` occurring only on the
right-hand side, unconstrained, so it could be taken large enough to empty the Grassmannian --
on `ℝ²` with `T = P = P' = id`, `E = ⊤`, `V = ⊥`, `l = 1`, `k = 5`, both hypotheses held while
the conclusion read `1 ≤ 0`.

The repair follows `proof_met.tex` l.352-356 exactly: `V, V' ∈ 𝒢^k X` (so `k` is pinned by the
*codimension* of `V`, via `GrassmannianCofin X k`, as in `Tsmallgrow`), and `P`, `P'` are the
projections *onto* `V`, `V'` -- `LinearMap.IsProj V P` gives `P x ∈ V` for all `x` and `P x = x`
on `V`, hence `X = V ⊕ ker P` with `P` the projection onto `V` along `E := ker P`.

Pinning `k` through `GrassmannianCofin` rather than through `finrank ℝ E = k` also matters: the
latter is satisfied by an *infinite-dimensional* `E` when `k = 0`, `finrank` being `0` by
convention in infinite dimension. `GrassmannianCofin` carries `FiniteDimensional ℝ (X ⧸ V)`
alongside the rank, so there is no junk-value hole.

`hPcompat` says `T` carries the splitting `V ⊕ E` to `V' ⊕ E'`: unfolding it gives `T V ⊆ V'`
and `T E ⊆ E'`. `hfast` says `E` is the fast space. `E'` and `ker P' = E'` are not named: they
are inert, since `IsProj V' P'` already supplies the splitting `X = V' ⊕ ker P'`.

**The proof (`proof_met.tex` l.357-367).** Let `R := ρ_l(T∘P)` and fix
`ε > 0`. Pick `U₀ ∈ 𝒢_l X` with `g_{T∘P}(U₀) > R - ε`; then `P` is injective on `U₀` and
`U := P U₀ ∈ 𝒢_l V` satisfies `g_T(U) ≥ g_{T∘P}(U₀)/‖P‖`. For a unit `x ∈ U ⊕ E`, write
`x = P x + (1 - P) x` with `P x ∈ U` and `(1 - P) x ∈ E`. Then `‖P' T x‖ = ‖T P x‖ ≥ g_T(U)‖P x‖`
and `‖(1 - P') T x‖ = ‖T (1 - P) x‖ ≥ g_T(E)‖(1 - P) x‖`, both by `hPcompat`, so

  `‖T x‖ ≥ max{‖P'Tx‖/‖P'‖, ‖(1-P')Tx‖/(1+‖P'‖)} ≥ g_T(U)·max{‖Px‖, ‖(1-P)x‖}/(1 + ‖P'‖)`,

using `g_T(E) ≥ g_T(U)` -- which is exactly what `hfast` buys, since `g_T(U) ≤ ‖T|_V‖ < g_T(E)`
for `U ≤ V`. As `max{‖Px‖, ‖(1-P)x‖} ≥ ‖x‖/2` and `1 + ‖P'‖ ≤ 2‖P'‖` for a nonzero projection
(`‖P'‖ ≥ 1`, from `‖P'‖ ≤ ‖P'‖²`), this gives `g_T(U ⊕ E) ≥ g_T(U)/(4‖P'‖) ≥ (R-ε)/(4‖P‖‖P'‖)`.
Since `U ⊕ E ∈ 𝒢_{l+k}X`, `ρ_{l+k}(T) ≥ (R-ε)/(4‖P‖‖P'‖)`; let `ε → 0`.

**Two departures from the paper's proof, both deliberate.**

1. *No `ρ_l(T|_V)`.* The paper routes through `ρ_l(T∘Π) ≤ ‖Π‖ρ_l(T|_V)`, but `ρ_l(T|_V)` is a
   Bernstein number of a map `V → V'` between *different* spaces, whereas `bernsteinNumber` here
   is defined only for an endomorphism. `exists_growth_ge_of_comp` gives the same content
   pointwise -- for each `U₀ ∈ 𝒢_l X`, an honest `U ≤ V` in `𝒢_l X` with
   `g_T(U) ≥ g_{T∘P}(U₀)/‖P‖` -- so no such number has to be named.
2. *No `ε`.* Working with each `U₀` separately rather than with the supremum removes the paper's
   `e^{-ε}` bookkeeping entirely; the bound on `ρ_l(T∘P)` then comes straight from `Real.sSup_le`.

Also, `max{‖Πx‖, ‖(1-Π)x‖} ≥ ½` is replaced by the equivalent `‖Πx‖ + ‖(1-Π)x‖ ≥ 1`, which
`nlinarith` handles without a case split.

Three degenerate cases are dispatched first: `P' = 0` (then `hPcompat` forces `T ∘ P = 0` and the
left side is `0`), `g_{T∘P}(U₀) ≤ 0` (immediate), and `l = 0` (which cannot occur once
`g_{T∘P}(U₀) > 0`, since `𝒢_0X = {⊥}` has empty unit sphere and `growth _ ⊥ = sInf ∅ = 0`). -/
theorem Tbiggrow (k l : ℕ) (V V' : GrassmannianCofin X k) (E : Submodule ℝ X)
    (P P' T : X →L[ℝ] X)
    (hPproj : LinearMap.IsProj (V.1.1 : Submodule ℝ X) (P : X →ₗ[ℝ] X))
    (hPker : LinearMap.ker (P : X →ₗ[ℝ] X) = E)
    (hP'proj : LinearMap.IsProj (V'.1.1 : Submodule ℝ X) (P' : X →ₗ[ℝ] X))
    (hPcompat : P'.comp T = T.comp P)
    (hfast : growth T E > ‖T.comp (V.1.1 : Submodule ℝ X).subtypeL‖) :
    bernsteinNumber (T.comp P) l ≤ 4 * ‖P‖ * ‖P'‖ * bernsteinNumber T (l + k) := by
  set Vs : Submodule ℝ X := (V.1.1 : Submodule ℝ X) with hVs
  have : FiniteDimensional ℝ (X ⧸ Vs) := V.2.1
  have hRHS : 0 ≤ 4 * ‖P‖ * ‖P'‖ * bernsteinNumber T (l + k) := by
    have := bernsteinNumber_nonneg T (l + k)
    have h1 : (0:ℝ) ≤ 4 * ‖P‖ * ‖P'‖ := by positivity
    exact mul_nonneg h1 this
  -- `P' = 0` forces `T ∘ P = 0`, and then the left-hand side is `0`
  by_cases hP'0 : P' = 0
  · have hTP : T.comp P = 0 := by
      rw [hP'0] at hPcompat
      simpa using hPcompat.symm
    rw [hTP]
    have : bernsteinNumber (0 : X →L[ℝ] X) l = 0 := by
      refine le_antisymm ?_ (bernsteinNumber_nonneg _ _)
      refine Real.sSup_le ?_ le_rfl
      rintro _ ⟨U, rfl⟩
      exact le_of_eq (growth_eq_zero_of_forall_eq_zero fun x _ => rfl)
    rw [this]
    exact hRHS
  have hP'norm : 1 ≤ ‖P'‖ := one_le_norm_of_isIdempotent
    (by ext x; exact hP'proj.map_id _ (hP'proj.map_mem x)) hP'0
  -- the splitting `X = Vs ⊕ E`
  have hcompl : IsCompl Vs E := hPker ▸ hPproj.isCompl
  have : FiniteDimensional ℝ E :=
    Module.Finite.equiv (Submodule.quotientEquivOfIsCompl Vs E hcompl)
  have hEdim : Module.finrank ℝ E = k := by
    rw [finrank_eq_of_isCompl_quotient hcompl]; exact V.2.2
  have hPzero : ∀ y ∈ E, P y = 0 := fun y hy => by
    rw [← hPker] at hy; exact hy
  have hcompat : ∀ y, P' (T y) = T (P y) := fun y => by
    have := congrArg (fun S : X →L[ℝ] X => S y) hPcompat
    simpa using this
  refine Real.sSup_le ?_ hRHS
  rintro _ ⟨U₀, rfl⟩
  rcases le_or_gt (growth (T.comp P) (U₀.1 : Submodule ℝ X)) 0 with hle | hpos
  · exact le_trans hle hRHS
  -- `l ≠ 0`, else the unit sphere of `U₀` is empty and the growth is `0`
  have : FiniteDimensional ℝ (U₀.1 : Submodule ℝ X) := U₀.2.1
  have hl : l ≠ 0 := by
    intro h0
    have hbot : (U₀.1 : Submodule ℝ X) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [U₀.2.2, h0])
    rw [hbot] at hpos
    have : growth (T.comp P) (⊥ : Submodule ℝ X) = 0 := by
      refine growth_eq_zero_of_forall_eq_zero fun x hx => ?_
      rw [Submodule.mem_bot] at hx
      rw [hx, map_zero]
    linarith
  obtain ⟨U, hUV, hUfin, hUdim, hUgrow⟩ :=
    exists_growth_ge_of_comp (V := Vs) hPproj.map_mem (U₀.1 : Submodule ℝ X) U₀.2.2 hpos
  have := hUfin
  have hUne : U ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hUdim
    exact hl hUdim.symm
  obtain ⟨u0, hu0U, hu0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  have hu0s : ‖u0‖⁻¹ • u0 ∈ Metric.sphere (0 : X) 1 ∩ (U : Set X) :=
    ⟨by rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu0ne)], U.smul_mem _ hu0U⟩
  -- `U` sits in the slow space, so `hfast` applies
  have hUE : growth T U ≤ growth T E := by
    refine le_of_lt (lt_of_le_of_lt ?_ hfast)
    have hmem : ‖u0‖⁻¹ • u0 ∈ Vs := hUV (U.smul_mem _ hu0U)
    have hbound : ‖T (‖u0‖⁻¹ • u0)‖ ≤ ‖T.comp Vs.subtypeL‖ := by
      have heq : ‖T (‖u0‖⁻¹ • u0)‖ = ‖(T.comp Vs.subtypeL) ⟨‖u0‖⁻¹ • u0, hmem⟩‖ := rfl
      rw [heq]
      calc ‖(T.comp Vs.subtypeL) ⟨‖u0‖⁻¹ • u0, hmem⟩‖
          ≤ ‖T.comp Vs.subtypeL‖ * ‖(⟨‖u0‖⁻¹ • u0, hmem⟩ : Vs)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖T.comp Vs.subtypeL‖ := by
            rw [show ‖(⟨‖u0‖⁻¹ • u0, hmem⟩ : Vs)‖ = ‖‖u0‖⁻¹ • u0‖ from rfl,
              norm_smul, norm_inv, norm_norm,
              inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu0ne), mul_one]
    refine le_trans ?_ hbound
    exact csInf_le ⟨0, by rintro _ ⟨z, -, rfl⟩; exact norm_nonneg _⟩ ⟨_, hu0s, rfl⟩
  -- the witness subspace for `ρ_{l+k}`
  have hWdim : Module.finrank ℝ (U ⊔ E : Submodule ℝ X) = l + k := by
    rw [finrank_sup_of_isCompl hcompl hUV, hUdim, hEdim]
  have : FiniteDimensional ℝ (U ⊔ E : Submodule ℝ X) := Submodule.finiteDimensional_sup U E
  have hWgrow : growth T U / (4 * ‖P'‖) ≤ growth T (U ⊔ E : Submodule ℝ X) := by
    refine le_csInf ⟨‖T (‖u0‖⁻¹ • u0)‖,
      ⟨_, ⟨hu0s.1, Submodule.mem_sup_left hu0s.2⟩, rfl⟩⟩ ?_
    rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
    exact Tbiggrow_pointwise (V := Vs) (E := E) (U := U) hPproj.map_id hPzero hcompat hUV hUE
      hP'norm hx2 (mem_sphere_zero_iff_norm.mp hx1)
  have hbern : growth T (U ⊔ E : Submodule ℝ X) ≤ bernsteinNumber T (l + k) := by
    refine le_csSup ⟨‖T‖, ?_⟩ ⟨⟨U ⊔ E, ⟨inferInstance, hWdim⟩⟩, rfl⟩
    rintro _ ⟨Z, rfl⟩
    exact growth_le_opNorm T _
  have hPne : P ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp only [ContinuousLinearMap.comp_zero] at hpos
    exact absurd (growth_eq_zero_of_forall_eq_zero (fun x _ => rfl)) (ne_of_gt hpos)
  have hPpos : 0 < ‖P‖ := norm_pos_iff.mpr hPne
  have hP'pos : (0:ℝ) < ‖P'‖ := lt_of_lt_of_le one_pos hP'norm
  rw [div_le_iff₀ hPpos] at hUgrow
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * ‖P'‖)] at hWgrow
  calc growth (T.comp P) (U₀.1 : Submodule ℝ X)
      ≤ growth T U * ‖P‖ := hUgrow
    _ ≤ growth T (U ⊔ E : Submodule ℝ X) * (4 * ‖P'‖) * ‖P‖ :=
        mul_le_mul_of_nonneg_right hWgrow (norm_nonneg P)
    _ ≤ bernsteinNumber T (l + k) * (4 * ‖P'‖) * ‖P‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbern (by positivity)) (norm_nonneg P)
    _ = 4 * ‖P‖ * ‖P'‖ * bernsteinNumber T (l + k) := by ring


end MultiplicativeErgodic
