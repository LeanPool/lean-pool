/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Grassmannian

/-!
# Measurable statistics for linear operators

Corresponds to Section 3 of `proof_met.tex`, plus the growth-function material at the start
of Section 2 (before Lemma \ref{GXsep}).
-/

@[expose] public section

namespace MultiplicativeErgodic

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- `g_T(V) = g(T,V)`: the slowest growth of vectors of the unit sphere of `V` under `T`. -/
noncomputable def growth (T : X →L[ℝ] Y) (V : Submodule ℝ X) : ℝ :=
  sInf ((fun x : X => ‖T x‖) '' (Metric.sphere (0 : X) 1 ∩ (V : Set X)))

/-- `ρ_k(T)`: the `k`-th Bernstein number, the sup of `g_T` over `k`-dimensional subspaces. -/
noncomputable def bernsteinNumber (T : X →L[ℝ] X) (k : ℕ) : ℝ :=
  sSup (Set.range fun V : GrassmannianFin X k => growth T (V.1 : Submodule ℝ X))

theorem growth_nonneg (T : X →L[ℝ] Y) (V : Submodule ℝ X) : 0 ≤ growth T V := by
  apply Real.sInf_nonneg
  rintro _ ⟨x, -, rfl⟩
  exact norm_nonneg _

theorem growth_le_opNorm (T : X →L[ℝ] Y) (V : Submodule ℝ X) : growth T V ≤ ‖T‖ := by
  rcases (Metric.sphere (0 : X) 1 ∩ (V : Set X)).eq_empty_or_nonempty with he | ⟨x, hx⟩
  · change sInf _ ≤ ‖T‖
    rw [he, Set.image_empty, Real.sInf_empty]
    exact norm_nonneg T
  · calc growth T V ≤ ‖T x‖ :=
          csInf_le ⟨0, by rintro _ ⟨z, -, rfl⟩; exact norm_nonneg _⟩ ⟨x, hx, rfl⟩
      _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
      _ = ‖T‖ := by rw [mem_sphere_zero_iff_norm.1 hx.1, mul_one]

/-- `ρ_k(T) ≤ ‖T‖`: the Bernstein numbers are bounded by the operator norm, being a supremum of
growth factors each of which is (`growth_le_opNorm`).

Needed to discharge Kingman's sharp hypothesis `∫ (f 1)⁺ < ∞` for the cocycle application: with
`f_n = log ρ_k(𝓛^{(n)})`, this gives `log⁺ ρ_k ≤ log⁺ ‖𝓛‖`, and the latter is integrable by a
cocycle's `forwardIntegrable` field. See `SubadditiveFamily.integrable_posPart`. -/
theorem bernsteinNumber_le_opNorm (T : X →L[ℝ] X) (k : ℕ) :
    bernsteinNumber T k ≤ ‖T‖ := by
  refine Real.sSup_le ?_ (norm_nonneg T)
  rintro _ ⟨V, rfl⟩
  exact growth_le_opNorm T _

/-- If `T` kills every vector of `V` (not just unit vectors), `g_T(V) = 0`: the defining set
either is empty (giving `sInf ∅ = 0`) or consists only of `0` (giving `sInf {0} = 0`). -/
theorem growth_eq_zero_of_forall_eq_zero {T : X →L[ℝ] Y} {V : Submodule ℝ X}
    (h : ∀ x ∈ V, T x = 0) : growth T V = 0 := by
  refine le_antisymm ?_ (growth_nonneg T V)
  rcases (Metric.sphere (0 : X) 1 ∩ (V : Set X)).eq_empty_or_nonempty with he | ⟨x, hx⟩
  · change sInf _ ≤ 0
    rw [he, Set.image_empty, Real.sInf_empty]
  · change sInf _ ≤ 0
    refine csInf_le ⟨0, ?_⟩ ⟨x, hx, ?_⟩
    · rintro _ ⟨y, -, rfl⟩; exact norm_nonneg _
    · simp [h x hx.2]

/-- Real-number epsilon-closing lemma: if `a ≤ b + c*ε` for every `ε > 0` (with `c ≥ 0` fixed),
then `a ≤ b`. Used to turn "for every `ε`, some vector gets within `ε` of the infimum" arguments
into the actual inequalities on `growth`. -/
theorem le_of_forall_pos_le_add_mul {a b c : ℝ} (hc : 0 ≤ c)
    (h : ∀ ε > 0, a ≤ b + c * ε) : a ≤ b := by
  by_contra hab
  rw [not_le] at hab
  rcases hc.eq_or_lt with hc0 | hc0
  · have h1 := h 1 one_pos
    rw [← hc0, zero_mul, add_zero] at h1
    linarith
  · have hd : (0 : ℝ) < (a - b) / (2 * c) := div_pos (by linarith) (by linarith)
    have hle := h _ hd
    have heq : c * ((a - b) / (2 * c)) = (a - b) / 2 := by
      have hcne : c ≠ 0 := hc0.ne'
      field_simp
    rw [heq] at hle
    linarith

/-- **Lemma \ref{growth_ineq}.** For `T : X →L[ℝ] Y` and `S : Y →L[ℝ] Z`,
`g_T(V) g_S(TV) ≤ g_{S∘T}(V) ≤ min{‖T‖ g_S(TV), g_T(V)‖S‖}` (we use the full operator norm
`‖T‖` in place of the paper's `‖T|_V‖`; since `‖T|_V‖ ≤ ‖T‖` this is a formally weaker, but
still correct and sufficient for downstream use, statement). -/
theorem growth_ineq (T : X →L[ℝ] Y) (S : Y →L[ℝ] Z) (V : Submodule ℝ X) :
    growth T V * growth S (V.map (T : X →ₗ[ℝ] Y)) ≤ growth (S.comp T) V ∧
    growth (S.comp T) V ≤ min (‖T‖ * growth S (V.map (T : X →ₗ[ℝ] Y))) (growth T V * ‖S‖) := by
  set W := V.map (T : X →ₗ[ℝ] Y) with hWdef
  by_cases hW : W = ⊥
  · -- `T` vanishes on all of `V`, so every growth statistic in sight is `0`.
    have hTV0 : ∀ x ∈ V, T x = 0 := by
      intro x hx
      have hmem : T x ∈ W := hWdef ▸ Submodule.mem_map_of_mem hx
      rwa [hW, Submodule.mem_bot] at hmem
    have hg1 : growth T V = 0 := growth_eq_zero_of_forall_eq_zero hTV0
    have hg2 : growth S W = 0 := by
      apply growth_eq_zero_of_forall_eq_zero
      intro y hy
      rw [hW, Submodule.mem_bot] at hy
      simp [hy]
    have hg3 : growth (S.comp T) V = 0 := by
      apply growth_eq_zero_of_forall_eq_zero
      intro x hx
      simp [ContinuousLinearMap.comp_apply, hTV0 x hx]
    rw [hg1, hg2, hg3]
    norm_num
  · -- The substantive case: `V ≠ ⊥` and `W ≠ ⊥`, so both unit spheres are nonempty.
    have hVne : V ≠ ⊥ := fun hVeq => hW (hWdef ▸ hVeq ▸ Submodule.map_bot _)
    set SV := Metric.sphere (0 : X) 1 ∩ (V : Set X) with hSVdef
    set SW := Metric.sphere (0 : Y) 1 ∩ (W : Set Y) with hSWdef
    have hSVne : SV.Nonempty := by
      obtain ⟨x0, hx0V, hx0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
      exact ⟨‖x0‖⁻¹ • x0,
        mem_sphere_zero_iff_norm.2
          (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0ne)]),
        V.smul_mem _ hx0V⟩
    have hSWne : SW.Nonempty := by
      obtain ⟨y0, hy0W, hy0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      exact ⟨‖y0‖⁻¹ • y0,
        mem_sphere_zero_iff_norm.2
          (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hy0ne)]),
        W.smul_mem _ hy0W⟩
    have claimA : growth T V * growth S W ≤ growth (S.comp T) V := by
      apply le_csInf (hSVne.image _)
      rintro _ ⟨x, ⟨hxs, hxV⟩, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hxs
      change growth T V * growth S W ≤ ‖(S.comp T) x‖
      rw [ContinuousLinearMap.comp_apply]
      have hTxle : growth T V ≤ ‖T x‖ :=
        csInf_le ⟨0, by rintro _ ⟨z, -, rfl⟩; exact norm_nonneg _⟩
          ⟨x, ⟨mem_sphere_zero_iff_norm.2 hxs, hxV⟩, rfl⟩
      rcases eq_or_ne (T x) 0 with hTx0 | hTx0
      · have hgt0 : growth T V = 0 := by
          have h0 : growth T V ≤ ‖T x‖ := hTxle
          rw [hTx0, norm_zero] at h0
          exact le_antisymm h0 (growth_nonneg T V)
        rw [hgt0, zero_mul, hTx0, map_zero, norm_zero]
      · set y := ‖T x‖⁻¹ • T x with hydef
        have hynorm : ‖y‖ = 1 := by
          rw [hydef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hTx0)]
        have hyW : y ∈ W := by
          rw [hWdef]
          exact W.smul_mem _ (hWdef ▸ Submodule.mem_map_of_mem hxV)
        have hgSW : growth S W ≤ ‖S y‖ :=
          csInf_le ⟨0, by rintro _ ⟨z, -, rfl⟩; exact norm_nonneg _⟩
            ⟨y, ⟨mem_sphere_zero_iff_norm.2 hynorm, hyW⟩, rfl⟩
        have hSy : ‖S y‖ = ‖T x‖⁻¹ * ‖S (T x)‖ := by
          rw [hydef, map_smul, norm_smul, norm_inv, norm_norm]
        rw [hSy] at hgSW
        have hTxpos : 0 < ‖T x‖ := norm_pos_iff.2 hTx0
        have hstep : ‖T x‖ * growth S W ≤ ‖S (T x)‖ := by
          have h2 := mul_le_mul_of_nonneg_left hgSW hTxpos.le
          rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hTxpos), one_mul] at h2
        calc growth T V * growth S W
            ≤ ‖T x‖ * growth S W := mul_le_mul_of_nonneg_right hTxle (growth_nonneg S W)
          _ ≤ ‖S (T x)‖ := hstep
    have claimB : growth (S.comp T) V ≤ ‖T‖ * growth S W := by
      apply le_of_forall_pos_le_add_mul (norm_nonneg T)
      intro ε hε
      obtain ⟨z, ⟨y, ⟨hys, hyW⟩, rfl⟩, hzlt⟩ :=
        exists_lt_of_csInf_lt (hSWne.image (fun y => ‖S y‖))
          (show growth S W < growth S W + ε by linarith)
      rw [mem_sphere_zero_iff_norm] at hys
      obtain ⟨x0, hx0V, hTeq⟩ := (Submodule.mem_map).1 (hWdef ▸ hyW)
      have hTeq' : T x0 = y := hTeq
      have hx00 : x0 ≠ 0 := by
        rintro rfl
        rw [map_zero] at hTeq'
        rw [← hTeq'] at hys
        simp at hys
      set x := ‖x0‖⁻¹ • x0 with hxdef
      have hxV : x ∈ V := V.smul_mem _ hx0V
      have hxnorm : ‖x‖ = 1 := by
        rw [hxdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx00)]
      have hTx : T x = ‖x0‖⁻¹ • y := by rw [hxdef, map_smul, hTeq']
      have hinvle : ‖x0‖⁻¹ ≤ ‖T‖ := by
        have h1 : ‖T x0‖ ≤ ‖T‖ * ‖x0‖ := T.le_opNorm _
        rw [hTeq', hys] at h1
        rw [← div_le_iff₀ (norm_pos_iff.2 hx00)] at h1
        simpa using h1
      have hgoal : growth (S.comp T) V ≤ ‖(S.comp T) x‖ :=
        csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact norm_nonneg _⟩
          ⟨x, ⟨mem_sphere_zero_iff_norm.2 hxnorm, hxV⟩, rfl⟩
      rw [ContinuousLinearMap.comp_apply] at hgoal
      have hSTx : ‖S (T x)‖ = ‖x0‖⁻¹ * ‖S y‖ := by
        rw [hTx, map_smul, norm_smul, norm_inv, norm_norm]
      rw [hSTx] at hgoal
      calc growth (S.comp T) V ≤ ‖x0‖⁻¹ * ‖S y‖ := hgoal
        _ ≤ ‖T‖ * ‖S y‖ := mul_le_mul_of_nonneg_right hinvle (norm_nonneg _)
        _ ≤ ‖T‖ * (growth S W + ε) := mul_le_mul_of_nonneg_left hzlt.le (norm_nonneg T)
        _ = ‖T‖ * growth S W + ‖T‖ * ε := by ring
    have claimC : growth (S.comp T) V ≤ growth T V * ‖S‖ := by
      apply le_of_forall_pos_le_add_mul (norm_nonneg S)
      intro ε hε
      obtain ⟨z, ⟨x, ⟨hxs, hxV⟩, rfl⟩, hzlt⟩ :=
        exists_lt_of_csInf_lt (hSVne.image (fun x => ‖T x‖))
          (show growth T V < growth T V + ε by linarith)
      rw [mem_sphere_zero_iff_norm] at hxs
      have hgoal : growth (S.comp T) V ≤ ‖(S.comp T) x‖ :=
        csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact norm_nonneg _⟩
          ⟨x, ⟨mem_sphere_zero_iff_norm.2 hxs, hxV⟩, rfl⟩
      rw [ContinuousLinearMap.comp_apply] at hgoal
      calc growth (S.comp T) V ≤ ‖S (T x)‖ := hgoal
        _ ≤ ‖S‖ * ‖T x‖ := S.le_opNorm _
        _ ≤ ‖S‖ * (growth T V + ε) := mul_le_mul_of_nonneg_left hzlt.le (norm_nonneg S)
        _ = growth T V * ‖S‖ + ‖S‖ * ε := by ring
    exact ⟨claimA, le_min claimB claimC⟩

open Classical in
/-- **The fastest volume growth `D_k`** (`proof_met.tex` l.207). The supremum, over `k`-tuples of
*unit* vectors `u` (no orthogonality is asked for, and none is available in a Banach space), of

  `∏ᵢ d(T uᵢ, span {T u_j : j < i})`,

the "volume" of the parallelepiped spanned by the images. Tuples that are not unit contribute `0`,
which is harmless: the supremum is over the unit ones. -/
noncomputable def volumeGrowth (T : X →L[ℝ] X) (k : ℕ) : ℝ :=
  sSup (Set.range fun u : Fin k → X =>
    if ∀ i, u i ∈ Metric.sphere (0 : X) 1 then
      ∏ i : Fin k, Metric.infDist (T (u i))
        ((Submodule.span ℝ ((fun j : Fin k => T (u j)) '' {j | j < i})) : Set X)
    else 0)

/-- The defining property of `growth`: `T` expands every vector of `V` by at least `g_T(V)`. -/
theorem growth_mul_norm_le {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X →L[ℝ] Y) {V : Submodule ℝ X} {u : X} (hu : u ∈ V) :
    growth T V * ‖u‖ ≤ ‖T u‖ := by
  rcases eq_or_ne u 0 with rfl | h0
  · simp
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr h0
  have hmem : ‖u‖⁻¹ • u ∈ Metric.sphere (0 : X) 1 ∩ (V : Set X) := by
    refine ⟨?_, V.smul_mem _ hu⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hupos)]
  have hle : growth T V ≤ ‖T (‖u‖⁻¹ • u)‖ :=
    csInf_le ⟨0, by rintro _ ⟨z, -, rfl⟩; exact norm_nonneg _⟩ ⟨_, hmem, rfl⟩
  rw [map_smul, norm_smul, norm_inv, norm_norm] at hle
  rw [← le_div_iff₀ hupos, div_eq_inv_mul]
  exact hle

/-- If `T` grows a subspace `V` at a strictly positive rate, `T` is injective on `V`: a nonzero
kernel vector in `V`, rescaled to the unit sphere, would witness `growth T V = 0`. -/
theorem injective_domRestrict_of_growth_pos {T : X →L[ℝ] X} {V : Submodule ℝ X}
    (h : 0 < growth T V) : Function.Injective (T.toLinearMap.domRestrict V) := by
  rw [LinearMap.injective_domRestrict_iff, Submodule.disjoint_def]
  intro x hxV hxker
  rw [LinearMap.mem_ker] at hxker
  by_contra hxne
  have hune : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hxne
  have humem : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : X) 1 ∩ (V : Set X) :=
    ⟨by rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hune],
     V.smul_mem _ hxV⟩
  have hTu0 : T (‖x‖⁻¹ • x) = 0 := by
    change T.toLinearMap (‖x‖⁻¹ • x) = 0
    rw [map_smul, hxker, smul_zero]
  have hle : growth T V ≤ ‖T (‖x‖⁻¹ • x)‖ :=
    csInf_le ⟨0, by rintro _ ⟨z, -, rfl⟩; exact norm_nonneg _⟩ ⟨_, humem, rfl⟩
  rw [hTu0, norm_zero] at hle
  linarith

/-- `ρ_k(T) ≥ 0` always: either no `k`-dimensional subspace exists (so the defining `sSup` is of
the empty set, `= 0` by convention), or every `g_T(V)` in the range is `≥ 0` (`growth_nonneg`) and
bounds `ρ_k(T)` from below. Needed to see `Θ > ρ_{k+1}(T)` forces `Θ > 0` in `pushclose`. -/
theorem bernsteinNumber_nonneg (T : X →L[ℝ] X) (k : ℕ) : 0 ≤ bernsteinNumber T k := by
  unfold bernsteinNumber
  rcases (Set.range fun V : GrassmannianFin X k =>
      growth T (V.1 : Submodule ℝ X)).eq_empty_or_nonempty
    with he | hne
  · rw [he, Real.sSup_empty]
  · obtain ⟨x, V, hV⟩ := hne
    have hbdd : BddAbove
        (Set.range fun V : GrassmannianFin X k => growth T (V.1 : Submodule ℝ X)) :=
      ⟨‖T‖, by rintro _ ⟨V', rfl⟩; exact growth_le_opNorm T V'.1⟩
    calc (0:ℝ) ≤ growth T (V.1 : Submodule ℝ X) := growth_nonneg T V.1
      _ = x := hV
      _ ≤ sSup _ := le_csSup hbdd ⟨V, hV⟩

/-- `g_T` on a line is just the norm of the image of a unit spanning vector: the unit sphere of
`span{u}` is `{u, -u}`. -/
theorem growth_span_singleton (T : X →L[ℝ] X) {u : X} (hu : ‖u‖ = 1) :
    growth T (Submodule.span ℝ {u}) = ‖T u‖ := by
  have hmem : u ∈ Metric.sphere (0 : X) 1 ∩ ((Submodule.span ℝ {u} : Submodule ℝ X) : Set X) :=
    ⟨mem_sphere_zero_iff_norm.2 hu, Submodule.mem_span_singleton_self u⟩
  refine le_antisymm (csInf_le ⟨0, by rintro _ ⟨z, -, rfl⟩; exact norm_nonneg _⟩ ⟨u, hmem, rfl⟩) ?_
  refine le_csInf ⟨‖T u‖, ⟨u, hmem, rfl⟩⟩ ?_
  rintro _ ⟨y, ⟨hys, hyV⟩, rfl⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hyV
  have hc : |c| = 1 := by
    have := mem_sphere_zero_iff_norm.1 hys
    rwa [norm_smul, hu, mul_one, Real.norm_eq_abs] at this
  change ‖T u‖ ≤ ‖T (c • u)‖
  rw [map_smul, norm_smul, Real.norm_eq_abs, hc, one_mul]

/-- `ρ_1(T) = ‖T‖`: the Bernstein supremum over lines is the operator norm. Both sides are `0`
when `X` is trivial, where there are no lines at all. -/
theorem bernsteinNumber_one (T : X →L[ℝ] X) : bernsteinNumber T 1 = ‖T‖ := by
  rcases subsingleton_or_nontrivial X with hs | hn
  · have hT : T = 0 := by
      ext x
      rw [Subsingleton.elim x 0]
      simp
    have hE : IsEmpty (GrassmannianFin X 1) := by
      refine ⟨fun V => ?_⟩
      have : FiniteDimensional ℝ (V.1 : Submodule ℝ X) := V.2.1
      have : Module.finrank ℝ (V.1 : Submodule ℝ X) = 0 := by
        have : Subsingleton (V.1 : Submodule ℝ X) := inferInstance
        simpa using Module.finrank_zero_of_subsingleton (R := ℝ) (M := (V.1 : Submodule ℝ X))
      rw [V.2.2] at this
      exact one_ne_zero this
    change sSup _ = _
    rw [Set.range_eq_empty, Real.sSup_empty, hT, norm_zero]
  · obtain ⟨x₀, hx₀⟩ := exists_ne (0 : X)
    have hline : ∀ u : X, ‖u‖ = 1 → Module.finrank ℝ (Submodule.span ℝ {u} : Submodule ℝ X) = 1 :=
      fun u hu => finrank_span_singleton (by rw [← norm_ne_zero_iff, hu]; norm_num)
    have hu₀ : ‖‖x₀‖⁻¹ • x₀‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx₀)]
    have : Nonempty (GrassmannianFin X 1) :=
      ⟨⟨Submodule.span ℝ {‖x₀‖⁻¹ • x₀},
        FiniteDimensional.span_of_finite ℝ (Set.finite_singleton _), hline _ hu₀⟩⟩
    refine le_antisymm (bernsteinNumber_le_opNorm T 1) ?_
    refine T.opNorm_le_bound (bernsteinNumber_nonneg T 1) fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hunorm : ‖‖x‖⁻¹ • x‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
      have hle : growth T (Submodule.span ℝ {‖x‖⁻¹ • x}) ≤ bernsteinNumber T 1 :=
        le_csSup ⟨‖T‖, by rintro _ ⟨V, rfl⟩; exact growth_le_opNorm T _⟩
          ⟨⟨Submodule.span ℝ {‖x‖⁻¹ • x},
            FiniteDimensional.span_of_finite ℝ (Set.finite_singleton _), hline _ hunorm⟩, rfl⟩
      rw [growth_span_singleton T hunorm, map_smul, norm_smul, norm_inv, norm_norm] at hle
      have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
      have hmul := mul_le_mul_of_nonneg_right hle hxpos.le
      calc ‖T x‖ = ‖x‖⁻¹ * ‖T x‖ * ‖x‖ := by field_simp
        _ ≤ bernsteinNumber T 1 * ‖x‖ := hmul

/-- `ρ_0(T) = 0`: the only `0`-dimensional subspace is `⊥`, on which `T` vanishes identically,
so every member of the defining range is `g_T(⊥) = 0`.

This is the junk index the `χ`-statements are shifted past (`χ_0 = ⊥`); it is recorded rather
than avoided because `Cocycle.exists_chi_ae_const` is stated for all `k`. -/
theorem bernsteinNumber_zero (T : X →L[ℝ] X) : bernsteinNumber T 0 = 0 := by
  refine le_antisymm (Real.sSup_le ?_ le_rfl) (bernsteinNumber_nonneg T 0)
  rintro _ ⟨V, rfl⟩
  have : FiniteDimensional ℝ (V.1 : Submodule ℝ X) := V.2.1
  have hbot : (V.1 : Submodule ℝ X) = ⊥ := Submodule.finrank_eq_zero.1 V.2.2
  refine le_of_eq (growth_eq_zero_of_forall_eq_zero ?_)
  intro x hx
  rw [hbot, Submodule.mem_bot] at hx
  simp [hx]

section VolumeGrowth

open Metric _root_.Submodule MultiplicativeErgodic.Submodule Module


/-- Distance to a submodule is unchanged by translating along it. -/
theorem infDist_add_mem (x : X) {W : Submodule ℝ X} {p : X} (hp : p ∈ W) :
    Metric.infDist (x + p) (W : Set X) = Metric.infDist x (W : Set X) := by
  have hiso : Isometry (fun y : X => y + p) := isometry_add_right p
  have himg : (fun y : X => y + p) '' (W : Set X) = (W : Set X) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩; exact W.add_mem hz hp
    · intro hy; exact ⟨y - p, W.sub_mem hy hp, by abel_nf⟩
  calc Metric.infDist (x + p) (W : Set X)
      = Metric.infDist ((fun y : X => y + p) x) ((fun y : X => y + p) '' (W : Set X)) := by
        rw [himg]
    _ = Metric.infDist x (W : Set X) := Metric.infDist_image hiso

theorem infDist_smul_le (c : ℝ) (x : X) (W : Submodule ℝ X) :
    Metric.infDist (c • x) (W : Set X) ≤ |c| * Metric.infDist x (W : Set X) := by
  have hne : (W : Set X).Nonempty := ⟨0, W.zero_mem⟩
  rcases eq_or_ne c 0 with rfl | hc
  · simp [Metric.infDist_zero_of_mem W.zero_mem]
  have hcpos : 0 < |c| := abs_pos.mpr hc
  rw [mul_comm, ← div_le_iff₀ hcpos, Metric.le_infDist hne]
  intro y hy
  rw [div_le_iff₀ hcpos]
  calc Metric.infDist (c • x) (W : Set X) ≤ dist (c • x) (c • y) :=
        Metric.infDist_le_dist_of_mem (W.smul_mem c hy)
    _ = |c| * dist x y := by
        rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs]
    _ = dist x y * |c| := mul_comm _ _

/-- Distance to a submodule scales. -/
theorem infDist_smul_submodule (c : ℝ) (x : X) (W : Submodule ℝ X) :
    Metric.infDist (c • x) (W : Set X) = |c| * Metric.infDist x (W : Set X) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [Metric.infDist_zero_of_mem W.zero_mem]
  refine le_antisymm (infDist_smul_le c x W) ?_
  have hcpos : 0 < |c| := abs_pos.mpr hc
  have h := infDist_smul_le c⁻¹ (c • x) W
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul, abs_inv] at h
  have h2 := mul_le_mul_of_nonneg_left h hcpos.le
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul] at h2
  exact h2

/-- Distance to a closed submodule vanishes exactly on the submodule. -/
theorem infDist_eq_zero_iff_mem {x : X} {W : Submodule ℝ X} (hW : IsClosed (W : Set X)) :
    Metric.infDist x (W : Set X) = 0 ↔ x ∈ W := by
  constructor
  · intro h
    have := (hW.mem_iff_infDist_zero ⟨0, W.zero_mem⟩).mpr h
    exact this
  · intro h
    exact Metric.infDist_zero_of_mem h

/-- The span of a finite family is closed. -/
theorem isClosed_span_image {k : ℕ} (v : Fin k → X) (s : Set (Fin k)) :
    IsClosed ((Submodule.span ℝ (v '' s) : Submodule ℝ X) : Set X) := by
  have : FiniteDimensional ℝ (Submodule.span ℝ (v '' s)) :=
    FiniteDimensional.span_of_finite ℝ ((Set.toFinite s).image v)
  exact Submodule.closed_of_finiteDimensional _

open Classical in
/-- The volume form `∏ᵢ d(T uᵢ, span{T u_j : j < i})`, of which `D_k` is the supremum over unit
tuples. -/
noncomputable def volForm (T : X →L[ℝ] X) {k : ℕ} (u : Fin k → X) : ℝ :=
  ∏ i : Fin k, Metric.infDist (T (u i))
    ((Submodule.span ℝ ((fun j : Fin k => T (u j)) '' {j | j < i})) : Set X)

open Classical in
theorem volumeGrowth_eq_sSup (T : X →L[ℝ] X) (k : ℕ) :
    volumeGrowth T k =
      sSup (Set.range fun u : Fin k → X =>
        if ∀ i, u i ∈ Metric.sphere (0 : X) 1 then volForm T u else 0) := rfl

theorem volForm_nonneg (T : X →L[ℝ] X) {k : ℕ} (u : Fin k → X) : 0 ≤ volForm T u :=
  Finset.prod_nonneg fun _ _ => Metric.infDist_nonneg

theorem volForm_le_pow (T : X →L[ℝ] X) {k : ℕ} {u : Fin k → X} (hu : ∀ i, ‖u i‖ = 1) :
    volForm T u ≤ ‖T‖ ^ k := by
  have hfac : ∀ i : Fin k, Metric.infDist (T (u i))
      ((Submodule.span ℝ ((fun j : Fin k => T (u j)) '' {j | j < i})) : Set X) ≤ ‖T‖ := by
    intro i
    calc Metric.infDist (T (u i)) _ ≤ dist (T (u i)) 0 :=
          Metric.infDist_le_dist_of_mem (Submodule.zero_mem _)
      _ = ‖T (u i)‖ := by rw [dist_zero_right]
      _ ≤ ‖T‖ * ‖u i‖ := T.le_opNorm _
      _ = ‖T‖ := by rw [hu i, mul_one]
  calc volForm T u ≤ ∏ _i : Fin k, ‖T‖ :=
        Finset.prod_le_prod₀ (fun _ _ => Metric.infDist_nonneg) (fun i _ => hfac i)
    _ = ‖T‖ ^ k := by simp

open Classical in
theorem bddAbove_volumeGrowth_set (T : X →L[ℝ] X) (k : ℕ) :
    BddAbove (Set.range fun u : Fin k → X =>
      if ∀ i, u i ∈ Metric.sphere (0 : X) 1 then volForm T u else 0) := by
  classical
  refine ⟨‖T‖ ^ k, ?_⟩
  rintro _ ⟨u, rfl⟩
  change (if ∀ i, u i ∈ Metric.sphere (0 : X) 1 then volForm T u else 0) ≤ ‖T‖ ^ k
  by_cases h : ∀ i, u i ∈ Metric.sphere (0 : X) 1
  · rw [ite_eq_left h]
    exact volForm_le_pow T fun i => mem_sphere_zero_iff_norm.mp (h i)
  · rw [ite_eq_right h]
    positivity

theorem volumeGrowth_nonneg (T : X →L[ℝ] X) (k : ℕ) : 0 ≤ volumeGrowth T k := by
  classical
  refine le_csSup_of_le (bddAbove_volumeGrowth_set T k)
    (Set.mem_range_self (f := fun u : Fin k → X =>
      if ∀ i, u i ∈ Metric.sphere (0 : X) 1 then volForm T u else 0) (fun _ => 0)) ?_
  change (0:ℝ) ≤ if ∀ i : Fin k, (0:X) ∈ Metric.sphere (0 : X) 1
    then volForm T (fun _ : Fin k => (0:X)) else 0
  split_ifs
  · exact volForm_nonneg _ _
  · exact le_rfl

theorem volForm_le_volumeGrowth (T : X →L[ℝ] X) {k : ℕ} {u : Fin k → X}
    (hu : ∀ i, ‖u i‖ = 1) : volForm T u ≤ volumeGrowth T k := by
  classical
  refine le_csSup (bddAbove_volumeGrowth_set T k) ⟨u, ?_⟩
  change (if ∀ i, u i ∈ Metric.sphere (0 : X) 1 then volForm T u else 0) = volForm T u
  rw [ite_eq_left fun i => mem_sphere_zero_iff_norm.mpr (hu i)]

/-- `S` maps the span of an initial segment onto the span of its image. -/
theorem map_span_image (S : X →L[ℝ] X) {k : ℕ} (v : Fin k → X) (A : Set (Fin k)) :
    Submodule.map (S : X →ₗ[ℝ] X) (Submodule.span ℝ (v '' A))
      = Submodule.span ℝ ((fun j => S (v j)) '' A) := by
  rw [Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨v j, ⟨j, hj, rfl⟩, rfl⟩

/-- If one factor of the identity volume form vanishes, so does the whole `S`-volume form:
a vector in the span of its predecessors stays there after applying `S`. -/
theorem volForm_eq_zero_of_factor_zero (S : X →L[ℝ] X) {k : ℕ} {v : Fin k → X} {i : Fin k}
    (h : Metric.infDist (v i) ((Submodule.span ℝ (v '' {j | j < i})) : Set X) = 0) :
    volForm S v = 0 := by
  have hmem : v i ∈ Submodule.span ℝ (v '' {j | j < i}) :=
    (infDist_eq_zero_iff_mem (isClosed_span_image v _)).mp h
  have hSmem : S (v i) ∈ Submodule.span ℝ ((fun j => S (v j)) '' {j | j < i}) := by
    rw [← map_span_image S v]
    exact ⟨v i, hmem, rfl⟩
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  exact (infDist_eq_zero_iff_mem (isClosed_span_image _ _)).mpr hSmem

/-- Replacing each `v i` by a normalised representative of `v i` modulo its predecessors does not
change the spans of initial segments. -/
theorem span_image_normalize {k : ℕ} {v w p : Fin k → X} {n : Fin k → ℝ}
    (hn : ∀ i, n i ≠ 0)
    (hp : ∀ i : Fin k, p i ∈ Submodule.span ℝ (v '' {j : Fin k | (j:ℕ) < (i:ℕ)}))
    (hw : ∀ i, w i = (n i)⁻¹ • (v i - p i)) :
    ∀ m : ℕ, Submodule.span ℝ (w '' {j : Fin k | (j:ℕ) < m})
      = Submodule.span ℝ (v '' {j : Fin k | (j:ℕ) < m}) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rcases lt_or_ge m k with hm | hm
    · have hset : ∀ u : Fin k → X, u '' {j : Fin k | (j:ℕ) < m + 1}
          = u '' {j : Fin k | (j:ℕ) < m} ∪ {u ⟨m, hm⟩} := by
        intro u
        ext y
        simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · rintro ⟨j, hj, rfl⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h1 | h1
          · exact Or.inl ⟨j, h1, rfl⟩
          · exact Or.inr (by rw [show j = (⟨m, hm⟩ : Fin k) from Fin.ext h1])
        · rintro (⟨j, hj, rfl⟩ | rfl)
          · exact ⟨j, by omega, rfl⟩
          · exact ⟨⟨m, hm⟩, by simp, rfl⟩
      have hpi : p ⟨m, hm⟩ ∈ Submodule.span ℝ (v '' {j : Fin k | (j:ℕ) < m}) := hp ⟨m, hm⟩
      rw [hset w, hset v, Submodule.span_union, Submodule.span_union, ih]
      refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
      · rw [Submodule.span_singleton_le_iff_mem, hw ⟨m, hm⟩]
        refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
        · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
        · exact Submodule.mem_sup_left hpi
      · rw [Submodule.span_singleton_le_iff_mem]
        have hvi : v ⟨m, hm⟩ = n ⟨m, hm⟩ • w ⟨m, hm⟩ + p ⟨m, hm⟩ := by
          rw [hw ⟨m, hm⟩, smul_smul, mul_inv_cancel₀ (hn ⟨m, hm⟩), one_smul]
          abel
        rw [hvi]
        refine Submodule.add_mem _ ?_ (Submodule.mem_sup_left hpi)
        exact Submodule.mem_sup_right
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    · have hsame : {j : Fin k | (j:ℕ) < m + 1} = {j : Fin k | (j:ℕ) < m} := by
        ext j; simp only [Set.mem_ofPred_eq]; omega
      rw [hsame, ih]

open Filter in
/-- **The key estimate.** For an arbitrary (not necessarily unit) tuple `v`, the `S`-volume form
is bounded by `D_k(S)` times the plain volume form of `v`. Everything else about
submultiplicativity follows from this. -/
theorem volForm_le_mul_prod (S : X →L[ℝ] X) {k : ℕ} (v : Fin k → X) :
    volForm S v ≤ volumeGrowth S k *
      ∏ i : Fin k, Metric.infDist (v i) ((Submodule.span ℝ (v '' {j | j < i})) : Set X) := by
  classical
  set d : Fin k → ℝ := fun i =>
    Metric.infDist (v i) ((Submodule.span ℝ (v '' {j | j < i})) : Set X) with hd
  have hdnn : ∀ i, 0 ≤ d i := fun _ => Metric.infDist_nonneg
  by_cases hzero : ∃ i, d i = 0
  · obtain ⟨i, hi⟩ := hzero
    rw [volForm_eq_zero_of_factor_zero S hi]
    have : ∏ i : Fin k, d i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [this, mul_zero]
  simp only [not_exists] at hzero
  have hdpos : ∀ i, 0 < d i := fun i => lt_of_le_of_ne (hdnn i) (Ne.symm (hzero i))
  -- for each `ε > 0` we build a unit tuple with the same spans
  have key : ∀ ε : ℝ, 0 < ε → volForm S v ≤ volumeGrowth S k * ∏ i : Fin k, (d i + ε) := by
    intro ε hε
    have hex : ∀ i : Fin k, ∃ y ∈ ((Submodule.span ℝ (v '' {j | j < i})) : Set X),
        dist (v i) y < d i + ε :=
      fun i => (Metric.infDist_lt_iff ⟨0, Submodule.zero_mem _⟩).mp
        (by change d i < d i + ε; linarith)
    choose p hpmem hpdist using hex
    set n : Fin k → ℝ := fun i => ‖v i - p i‖ with hn
    have hnd : ∀ i, d i ≤ n i := fun i => by
      change d i ≤ ‖v i - p i‖
      simpa [dist_eq_norm] using Metric.infDist_le_dist_of_mem (hpmem i)
    have hnpos : ∀ i, 0 < n i := fun i => lt_of_lt_of_le (hdpos i) (hnd i)
    have hnlt : ∀ i, n i < d i + ε := fun i => by
      change ‖v i - p i‖ < d i + ε
      simpa [dist_eq_norm] using hpdist i
    set w : Fin k → X := fun i => (n i)⁻¹ • (v i - p i) with hwdef
    have hwnorm : ∀ i, ‖w i‖ = 1 := by
      intro i
      change ‖(n i)⁻¹ • (v i - p i)‖ = 1
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hnpos i)]
      change (n i)⁻¹ * n i = 1
      exact inv_mul_cancel₀ (ne_of_gt (hnpos i))
    -- the spans of initial segments are unchanged
    have hpmem' : ∀ i : Fin k, p i ∈ Submodule.span ℝ (v '' {j : Fin k | (j:ℕ) < (i:ℕ)}) :=
      fun i => hpmem i
    have hspanN := span_image_normalize (v := v) (w := w) (p := p) (n := n)
      (fun i => ne_of_gt (hnpos i)) hpmem' (fun i => rfl)
    have hspan : ∀ i : Fin k, Submodule.span ℝ (w '' {j | j < i})
        = Submodule.span ℝ (v '' {j | j < i}) := fun i => hspanN (i : ℕ)
    -- the per-factor identity
    have hfac : ∀ i : Fin k,
        Metric.infDist (S (w i))
          ((Submodule.span ℝ ((fun j => S (w j)) '' {j | j < i})) : Set X) * n i
        = Metric.infDist (S (v i))
          ((Submodule.span ℝ ((fun j => S (v j)) '' {j | j < i})) : Set X) := by
      intro i
      have hW : Submodule.span ℝ ((fun j => S (w j)) '' {j | j < i})
          = Submodule.span ℝ ((fun j => S (v j)) '' {j | j < i}) := by
        rw [← map_span_image S w, ← map_span_image S v, hspan i]
      have hSp : S (p i) ∈ Submodule.span ℝ ((fun j => S (v j)) '' {j | j < i}) := by
        rw [← map_span_image S v]
        exact ⟨p i, hpmem i, rfl⟩
      have hSw : S (w i) = (n i)⁻¹ • (S (v i) + (-(S (p i)))) := by
        rw [hwdef]
        simp only [map_smul, map_sub]
        congr 1
        abel
      rw [hW, hSw, infDist_smul_submodule, infDist_add_mem _ (Submodule.neg_mem _ hSp),
        abs_of_pos (inv_pos.mpr (hnpos i))]
      field_simp
      rw [mul_comm, mul_div_assoc, div_self (ne_of_gt (hnpos i)), mul_one]
    have hprod : volForm S w * ∏ i : Fin k, n i = volForm S v := by
      rw [volForm, volForm, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => hfac i
    calc volForm S v = volForm S w * ∏ i : Fin k, n i := hprod.symm
      _ ≤ volumeGrowth S k * ∏ i : Fin k, (d i + ε) := by
          refine mul_le_mul (volForm_le_volumeGrowth S hwnorm) ?_
            (Finset.prod_nonneg fun i _ => (hnpos i).le) (volumeGrowth_nonneg S k)
          exact Finset.prod_le_prod₀ (fun i _ => (hnpos i).le) (fun i _ => (hnlt i).le)
  -- let `ε → 0`
  have hcont : Filter.Tendsto (fun ε : ℝ => volumeGrowth S k * ∏ i : Fin k, (d i + ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (volumeGrowth S k * ∏ i : Fin k, d i)) := by
    have h1 : Continuous fun ε : ℝ => volumeGrowth S k * ∏ i : Fin k, (d i + ε) :=
      continuous_const.mul (continuous_finsetProd _ fun i _ => continuous_const.add continuous_id)
    have h2 : Filter.Tendsto (fun ε : ℝ => volumeGrowth S k * ∏ i : Fin k, (d i + ε))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (volumeGrowth S k * ∏ i : Fin k, (d i + 0))) :=
      (h1.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h2
  refine ge_of_tendsto hcont ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact key ε hε

open Classical in
/-- **`D_k` is submultiplicative.** -/
theorem volumeGrowth_submultiplicative (k : ℕ) (T S : X →L[ℝ] X) :
    volumeGrowth (S.comp T) k ≤ volumeGrowth S k * volumeGrowth T k := by
  classical
  refine Real.sSup_le ?_ (mul_nonneg (volumeGrowth_nonneg S k) (volumeGrowth_nonneg T k))
  rintro _ ⟨u, rfl⟩
  change (if ∀ i, u i ∈ Metric.sphere (0 : X) 1 then volForm (S.comp T) u else 0)
    ≤ volumeGrowth S k * volumeGrowth T k
  by_cases h : ∀ i, u i ∈ Metric.sphere (0 : X) 1
  · rw [ite_eq_left h]
    have hu : ∀ i, ‖u i‖ = 1 := fun i => mem_sphere_zero_iff_norm.mp (h i)
    have h1 : volForm (S.comp T) u = volForm S (fun i => T (u i)) := rfl
    rw [h1]
    calc volForm S (fun i => T (u i))
        ≤ volumeGrowth S k * ∏ i : Fin k, Metric.infDist ((fun i => T (u i)) i)
            ((Submodule.span ℝ ((fun i => T (u i)) '' {j | j < i})) : Set X) :=
          volForm_le_mul_prod S _
      _ = volumeGrowth S k * volForm T u := rfl
      _ ≤ volumeGrowth S k * volumeGrowth T k :=
          mul_le_mul_of_nonneg_left (volForm_le_volumeGrowth T hu) (volumeGrowth_nonneg S k)
  · rw [ite_eq_right h]
    exact mul_nonneg (volumeGrowth_nonneg S k) (volumeGrowth_nonneg T k)

end VolumeGrowth

end MultiplicativeErgodic
