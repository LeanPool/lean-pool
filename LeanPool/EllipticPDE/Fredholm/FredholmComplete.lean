/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Fredholm.Fredholm
public import Mathlib.Analysis.InnerProductSpace.Spectrum


/-!
# Complete Fredholm theory

Evans §6.2.3, Theorem 4.

`Fredholm.lean` reduces the weak problem `Lu = f` to the compact-operator equation
`(1 - opK)u = h` through the factorisation `opA = opE ∘ (1 - opK)` and derives the
dichotomy. This module begins the *quantitative* part of Evans's Theorem 4(ii)
(§6.2.3): the space

  `N = {u ∈ H₀¹(Ω) : B[u, v] = 0 for all v}`

of weak solutions of the homogeneous problem is **finite-dimensional**. Since `opE` is a
continuous linear equivalence, `N = ker(opA) = ker(1 - opK)` is the eigenspace of the
compact operator `opK` at the eigenvalue `1`, and eigenspaces of compact operators at
nonzero eigenvalues are finite-dimensional
(`ContinuousLinearMap.finite_dimensional_eigenspace`, the Riesz theory input).

Remaining for the full Theorem 4(ii)/(iii) statement (planned here): closed range of
`1 - opK`, the adjoint problem via the transpose form `B(·, v)`, the solvability
criterion `Lu = f` solvable ↔ `f ⊥ N*`, and `dim N = dim N*`.
-/

@[expose] public section

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

/-! ### Riesz theory for `1 - K` with `K` compact on a real Hilbert space -/

section RieszTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {K : E →L[ℝ] E}

omit [CompleteSpace E] in
/-- The kernel of `1 - K` is the eigenspace of `K` at the eigenvalue `1`. -/
lemma ker_one_sub_eq_eigenspace (K : E →L[ℝ] E) :
    LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap
      = Module.End.eigenspace K.toLinearMap 1 := by
  ext u
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Module.End.mem_eigenspace_iff, one_smul,
    _root_.sub_apply, one_apply_eq_self, sub_eq_zero]
  exact eq_comm

/-- **Finite-dimensionality of `ker(1 - K)`** for a compact operator `K` (Riesz
theory): the kernel is the eigenspace of `K` at the nonzero eigenvalue `1`. -/
theorem finiteDimensional_ker_one_sub (hK : IsCompactOperator K) :
    FiniteDimensional ℝ (LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap) := by
  rw [ker_one_sub_eq_eigenspace]
  exact ContinuousLinearMap.finite_dimensional_eigenspace hK 1 one_ne_zero

omit [CompleteSpace E] in
/-- `1 - K` is **bounded below on the orthogonal complement of its kernel**: the main step of
the Riesz closed-range theorem, by the standard compactness contradiction. If not, normalised
`xₙ ∈ (ker(1-K))ᗮ` have `(1-K)xₙ → 0`; compactness of `K` extracts `Kx_{φ(n)} → z`, so `x_{φ(n)}
→ z` with `‖z‖ = 1`, `z ∈ ker(1-K)`, and `z ∈ (ker(1-K))ᗮ`, forcing `z = 0` against `‖z‖ = 1`. -/
theorem exists_pos_bound_on_orthogonal_ker (hK : IsCompactOperator K) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ (LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap)ᗮ,
      c * ‖x‖ ≤ ‖(1 - K : E →L[ℝ] E) x‖ := by
  set N := LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap with hN
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ x : E,
      x ∈ Nᗮ ∧ ‖x‖ = 1 ∧ ‖(1 - K : E →L[ℝ] E) x‖ < 1 / (n + 1) := by
    intro n
    obtain ⟨x, hxmem, hxlt⟩ := hcon (1 / (n + 1)) (by positivity)
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hxlt
    have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
    refine ⟨‖x‖⁻¹ • x, Submodule.smul_mem _ _ hxmem, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn]
    · rw [map_smul, norm_smul, norm_inv, norm_norm]
      calc ‖x‖⁻¹ * ‖(1 - K : E →L[ℝ] E) x‖
          < ‖x‖⁻¹ * (1 / (n + 1) * ‖x‖) :=
            mul_lt_mul_of_pos_left hxlt (by positivity)
        _ = 1 / (n + 1) * (‖x‖⁻¹ * ‖x‖) := by ring
        _ = 1 / (n + 1) := by rw [inv_mul_cancel₀ hxn, mul_one]
  choose y hymem hynorm hylt using hseq
  -- the images `K yₙ` live in a compact set; extract a convergent subsequence
  have hK' : IsCompactOperator K.toLinearMap := hK
  have hcpt : IsCompact (closure (K.toLinearMap '' Metric.closedBall 0 1)) :=
    hK'.isCompact_closure_image_closedBall 1
  have hmem : ∀ n : ℕ, K (y n) ∈ closure (K.toLinearMap '' Metric.closedBall 0 1) :=
    fun n => subset_closure ⟨y n, mem_closedBall_zero_iff.mpr (le_of_eq (hynorm n)), rfl⟩
  obtain ⟨z, -, φ, hφ, hzlim⟩ := hcpt.tendsto_subseq hmem
  -- `(1 - K) y_{φ(n)} → 0` by the squeeze
  have hbound : ∀ n : ℕ, ‖(1 - K : E →L[ℝ] E) (y (φ n))‖ ≤ 1 / (n + 1) := by
    intro n
    refine (hylt (φ n)).le.trans ?_
    have h1 : (n : ℝ) + 1 ≤ (φ n : ℝ) + 1 := by
      have hn : n ≤ φ n := hφ.le_apply
      exact_mod_cast Nat.add_le_add_right hn 1
    exact one_div_le_one_div_of_le (by positivity) h1
  have h1K : Filter.Tendsto (fun n => (1 - K : E →L[ℝ] E) (y (φ n)))
      Filter.atTop (nhds 0) :=
    squeeze_zero_norm hbound tendsto_one_div_add_atTop_nhds_zero_nat
  -- the subsequence itself converges to `z`
  have hy_lim : Filter.Tendsto (fun n => y (φ n)) Filter.atTop (nhds z) := by
    have hsum : (fun n => y (φ n))
        = fun n => (1 - K : E →L[ℝ] E) (y (φ n)) + K (y (φ n)) := by
      funext n
      rw [_root_.sub_apply, one_apply_eq_self, sub_add_cancel]
    rw [hsum]
    simpa [Function.comp] using h1K.add hzlim
  -- `z` has norm one, lies in `Nᗮ` (closed), and lies in `N` (continuity): contradiction
  have hznorm : ‖z‖ = 1 := by
    have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds ‖z‖) :=
      hy_lim.norm.congr (fun n => hynorm (φ n))
    exact tendsto_nhds_unique hconst tendsto_const_nhds
  have hz_orth : z ∈ Nᗮ :=
    N.isClosed_orthogonal.mem_of_tendsto hy_lim
      (Filter.Eventually.of_forall (fun n => hymem (φ n)))
  have hz_ker : z ∈ N := by
    have hcont : Filter.Tendsto (fun n => (1 - K : E →L[ℝ] E) (y (φ n)))
        Filter.atTop (nhds ((1 - K : E →L[ℝ] E) z)) :=
      (((1 - K : E →L[ℝ] E).continuous.tendsto z).comp hy_lim)
    have hz0 : (1 - K : E →L[ℝ] E) z = 0 := tendsto_nhds_unique hcont h1K
    rw [hN, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    exact hz0
  have hz_zero : z = 0 := (Submodule.mem_bot ℝ).mp
    (N.orthogonal_disjoint.le_bot (Submodule.mem_inf.mpr ⟨hz_ker, hz_orth⟩))
  rw [hz_zero, norm_zero] at hznorm
  exact zero_ne_one hznorm

/-- **Closed range (Riesz theory).** For a compact operator `K` on a real Hilbert
space the range of `1 - K` is closed: `1 - K` is bounded below (hence antilipschitzWith
with closed range) on the orthogonal complement of its finite-dimensional kernel, and
the full range is the image of that complement. This is the geometric half towards
Evans's Theorem 4(ii) (§6.2.3). -/
theorem isClosed_range_one_sub (hK : IsCompactOperator K) :
    IsClosed (Set.range (1 - K : E →L[ℝ] E)) := by
  obtain ⟨c, hc, hbdd⟩ := exists_pos_bound_on_orthogonal_ker hK
  set N := LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap with hN
  have : FiniteDimensional ℝ N := finiteDimensional_ker_one_sub hK
  set T : Nᗮ →L[ℝ] E := (1 - K : E →L[ℝ] E).comp Nᗮ.subtypeL with hT
  have hbT : ∀ x : Nᗮ, ‖x‖ ≤ c⁻¹ * ‖T x‖ := by
    intro x
    have hx : c * ‖x‖ ≤ ‖T x‖ := hbdd (x : E) x.2
    have h := mul_le_mul_of_nonneg_left hx (le_of_lt (inv_pos.mpr hc))
    rwa [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at h
  have hanti : AntilipschitzWith (c⁻¹).toNNReal T :=
    T.antilipschitz_of_bound (fun x => by
      have h := hbT x
      rwa [← Real.coe_toNNReal c⁻¹ (by positivity)] at h)
  have hTclosed : IsClosed (Set.range T) :=
    hanti.isClosed_range T.uniformContinuous
  have hrange : Set.range ((1 - K : E →L[ℝ] E)) = Set.range T := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨n, hn, m, hm, rfl⟩ := N.exists_add_mem_mem_orthogonal x
      refine ⟨⟨m, hm⟩, ?_⟩
      have hn0 : (1 - K : E →L[ℝ] E) n = 0 := by
        rw [hN, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hn
        exact hn
      change (1 - K : E →L[ℝ] E) m = (1 - K : E →L[ℝ] E) (n + m)
      rw [map_add, hn0, zero_add]
    · rintro ⟨m, rfl⟩
      exact ⟨(m : E), rfl⟩
  rw [hrange]
  exact hTclosed

/-- A closed-range operator on a real Hilbert space has range exactly the orthogonal
complement of the kernel of its adjoint: `range A = (ker A†)ᗮ`. With
`isClosed_range_one_sub` this yields the solvability half of the Fredholm
alternative. -/
lemma range_eq_orthogonal_ker_adjoint (A : E →L[ℝ] E)
    (hA : IsClosed (Set.range A)) :
    LinearMap.range A.toLinearMap
      = (LinearMap.ker (ContinuousLinearMap.adjoint A).toLinearMap)ᗮ := by
  have h1 : (LinearMap.range A.toLinearMap)ᗮ
      = LinearMap.ker (ContinuousLinearMap.adjoint A).toLinearMap :=
    ContinuousLinearMap.orthogonal_range A
  rw [← h1, Submodule.orthogonal_orthogonal_eq_closure]
  refine (IsClosed.submodule_topologicalClosure_eq ?_).symm
  rw [LinearMap.coe_range]
  exact hA

/-- **Schauder's theorem** on a real Hilbert space: the adjoint of a compact operator
is compact. The Hilbert-space proof:
`‖K†x - K†y‖² = ⟪x - y, KK†(x - y)⟫ ≤ ‖x - y‖ ‖KK†x - KK†y‖`, so an `ε²/8`-net for
the relatively compact image `KK†(B)` of the unit ball pulls back to an `ε`-net for
`K†(B)`, making `K†(B)` totally bounded. -/
theorem isCompactOperator_adjoint (hK : IsCompactOperator K) :
    IsCompactOperator (ContinuousLinearMap.adjoint K) := by
  classical
  set Kd : E →L[ℝ] E := ContinuousLinearMap.adjoint K with hKddef
  -- the composition `K ∘ K†` is compact
  have hKKd : IsCompactOperator (K.comp Kd).toLinearMap := hK.comp_clm Kd
  -- the image of the unit ball under `K†` is totally bounded
  have key : TotallyBounded (Kd '' Metric.ball 0 1) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    set δ : ℝ := ε ^ 2 / 8 with hδdef
    have hδ : 0 < δ := by positivity
    -- a `δ`-net for `KK†(B)` from compactness
    have htbKK : TotallyBounded ((K.comp Kd).toLinearMap '' Metric.ball 0 1) :=
      (hKKd.isCompact_closure_image_ball 1).totallyBounded.subset subset_closure
    rw [Metric.totallyBounded_iff] at htbKK
    obtain ⟨t, htfin, htcover⟩ := htbKK δ hδ
    -- choose a representative preimage for each useful net centre
    set pick : E → E := fun c =>
      if h : ∃ x, x ∈ Metric.ball (0 : E) 1 ∧ (K.comp Kd) x ∈ Metric.ball c δ
      then h.choose else 0 with hpickdef
    refine ⟨(fun c => Kd (pick c)) '' t, htfin.image _, ?_⟩
    rintro w ⟨x, hx, rfl⟩
    have hKx : (K.comp Kd).toLinearMap x ∈ ⋃ c ∈ t, Metric.ball c δ :=
      htcover ⟨x, hx, rfl⟩
    rw [Set.mem_iUnion₂] at hKx
    obtain ⟨c, hct, hcball⟩ := hKx
    have hex : ∃ x', x' ∈ Metric.ball (0 : E) 1 ∧ (K.comp Kd) x' ∈ Metric.ball c δ :=
      ⟨x, hx, hcball⟩
    have hpc : pick c ∈ Metric.ball (0 : E) 1 ∧ (K.comp Kd) (pick c) ∈ Metric.ball c δ := by
      rw [hpickdef]
      simp only [dite_eq_left hex]
      exact hex.choose_spec
    rw [Set.mem_iUnion₂]
    refine ⟨Kd (pick c), ⟨c, hct, rfl⟩, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    -- the inner-product estimate
    set z : E := x - pick c with hzdef
    have hsq : ‖Kd x - Kd (pick c)‖ ^ 2
        ≤ ‖z‖ * ‖(K.comp Kd) x - (K.comp Kd) (pick c)‖ := by
      have h1 : ‖Kd x - Kd (pick c)‖ ^ 2 = ⟪z, (K.comp Kd) z⟫ := by
        rw [← map_sub, ← real_inner_self_eq_norm_sq]
        rw [show (K.comp Kd) z = K (Kd z) from rfl]
        exact ContinuousLinearMap.adjoint_inner_left K (Kd z) z
      have h2 : ⟪z, (K.comp Kd) z⟫ ≤ ‖z‖ * ‖(K.comp Kd) z‖ := real_inner_le_norm _ _
      have h3 : (K.comp Kd) z = (K.comp Kd) x - (K.comp Kd) (pick c) := map_sub _ _ _
      rw [h1, ← h3]
      exact h2
    have hz2 : ‖z‖ ≤ 2 := by
      calc ‖z‖ ≤ ‖x‖ + ‖pick c‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (mem_ball_zero_iff.mp hx).le (mem_ball_zero_iff.mp hpc.1).le
        _ = 2 := by norm_num
    have hKK2 : ‖(K.comp Kd) x - (K.comp Kd) (pick c)‖ < 2 * δ := by
      calc ‖(K.comp Kd) x - (K.comp Kd) (pick c)‖
          ≤ dist ((K.comp Kd) x) c + dist c ((K.comp Kd) (pick c)) := by
            rw [← dist_eq_norm]
            exact dist_triangle _ _ _
        _ < δ + δ := add_lt_add (Metric.mem_ball.mp hcball)
            (by rw [dist_comm]; exact Metric.mem_ball.mp hpc.2)
        _ = 2 * δ := by ring
    -- conclude `‖K†x - K†(pick c)‖ < ε`
    have hfinal : ‖Kd x - Kd (pick c)‖ ^ 2 < ε ^ 2 := by
      have hb : ‖z‖ * ‖(K.comp Kd) x - (K.comp Kd) (pick c)‖ ≤ 2 * (2 * δ) := by
        have hnn : (0 : ℝ) ≤ ‖(K.comp Kd) x - (K.comp Kd) (pick c)‖ := norm_nonneg _
        nlinarith [hz2, hKK2.le, hnn, norm_nonneg z]
      have : ‖Kd x - Kd (pick c)‖ ^ 2 ≤ 2 * (2 * δ) := le_trans hsq hb
      have hδε : 2 * (2 * δ) < ε ^ 2 := by
        rw [hδdef]; nlinarith [hε]
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hfinal
  -- totally bounded + complete codomain: the closure is compact
  have hcompact : IsCompact (closure (Kd.toLinearMap '' Metric.ball 0 1)) :=
    key.closure.isCompact_of_isComplete isClosed_closure.isComplete
  exact (isCompactOperator_iff_isCompact_closure_image_ball
    Kd.toLinearMap one_pos).mpr hcompact

/-- The adjoint of `1 - K` is `1 - K†`. -/
lemma adjoint_one_sub (K : E →L[ℝ] E) :
    ContinuousLinearMap.adjoint (1 - K : E →L[ℝ] E)
      = 1 - ContinuousLinearMap.adjoint K := by
  ext x
  apply ext_inner_left ℝ
  intro y
  simp only [ContinuousLinearMap.adjoint_inner_right,
    sub_apply, one_apply_eq_self,
    inner_sub_left, inner_sub_right]

/-- **Equal (finite) dimension of the two kernels**, one inequality. If
`dim ker(1-K) < dim ker(1-K†)` then an injective, non-surjective linear map
`Λ : ker(1-K) → ker(1-K†)` composed with the orthogonal projection gives a finite-rank
perturbation `S = K + Λ∘P` with `1 - S` injective; the Fredholm alternative makes
`1 - S` surjective, yet nothing outside `range Λ` is attained, a contradiction
(Brezis Thm 6.6 adapted to the Hilbert setting). -/
theorem finrank_ker_one_sub_adjoint_le (hK : IsCompactOperator K) :
    Module.finrank ℝ
      (LinearMap.ker ((1 - ContinuousLinearMap.adjoint K : E →L[ℝ] E)).toLinearMap)
      ≤ Module.finrank ℝ (LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap) := by
  set N := LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap with hN
  set Nstar := LinearMap.ker
    ((1 - ContinuousLinearMap.adjoint K : E →L[ℝ] E)).toLinearMap with hNstar
  have hNfin : FiniteDimensional ℝ N := finiteDimensional_ker_one_sub hK
  have hNstarfin : FiniteDimensional ℝ Nstar :=
    finiteDimensional_ker_one_sub (isCompactOperator_adjoint hK)
  by_contra hcon
  push Not at hcon
  -- an injective, non-surjective linear map `N → N*`
  have hrank : Module.rank ℝ N < Module.rank ℝ Nstar := by
    rw [← Module.finrank_eq_rank ℝ N, ← Module.finrank_eq_rank ℝ Nstar]
    exact_mod_cast hcon
  obtain ⟨Λ, hΛinj⟩ := Module.Free.exists_linearMap_injective_of_rank_lt hrank
  have hΛrange : LinearMap.range Λ ≠ ⊤ := by
    intro htop
    have h1 : Module.finrank ℝ (LinearMap.range Λ) ≤ Module.finrank ℝ N :=
      LinearMap.finrank_range_le Λ
    rw [htop, finrank_top] at h1
    exact absurd (lt_of_lt_of_le hcon h1) (lt_irrefl _)
  obtain ⟨ystar, hystar⟩ : ∃ y : Nstar, y ∉ LinearMap.range Λ := by
    by_contra hall
    push Not at hall
    exact hΛrange (Submodule.eq_top_iff'.mpr hall)
  -- the finite-rank perturbation `Φ = incl ∘ Λ ∘ P`
  set Φ : E →L[ℝ] E :=
    Nstar.subtypeL.comp
      ((LinearMap.toContinuousLinearMap Λ).comp N.orthogonalProjectionOnto) with hΦdef
  have hΦmem : ∀ u : E, Φ u ∈ Nstar := fun u => SetLike.coe_mem _
  have hΦcompact : IsCompactOperator Φ := by
    have hg : IsCompactOperator
        ((LinearMap.toContinuousLinearMap Λ).comp N.orthogonalProjectionOnto) :=
      isCompactOperator_of_locallyCompactSpace_dom _
    exact hg.clm_comp Nstar.subtypeL
  set S : E →L[ℝ] E := K + Φ with hSdef
  have hScompact : IsCompactOperator S := hK.add hΦcompact
  -- the range identity for `1 - K`
  have hrangeNstar : LinearMap.range ((1 - K : E →L[ℝ] E)).toLinearMap = Nstarᗮ := by
    rw [hNstar, ← adjoint_one_sub K]
    exact range_eq_orthogonal_ker_adjoint _ (isClosed_range_one_sub hK)
  -- `1 - S` is injective
  have hSker : ∀ u : E, (1 - S) u = 0 → u = 0 := by
    intro u hu
    have hsplit : (1 - K : E →L[ℝ] E) u = Φ u := by
      have h1 : (1 - S) u = (1 - K : E →L[ℝ] E) u - Φ u := by
        simp only [hSdef, _root_.sub_apply, one_apply_eq_self,
          _root_.add_apply]
        abel
      rw [h1, sub_eq_zero] at hu
      exact hu
    -- the common value lies in `Nstar ⊓ Nstarᗮ = ⊥`
    have hmem1 : (1 - K : E →L[ℝ] E) u ∈ Nstarᗮ := by
      rw [← hrangeNstar]
      exact ⟨u, rfl⟩
    have hmem2 : (1 - K : E →L[ℝ] E) u ∈ Nstar := hsplit ▸ hΦmem u
    have hzero : (1 - K : E →L[ℝ] E) u = 0 := (Submodule.mem_bot ℝ).mp
      (Nstar.orthogonal_disjoint.le_bot (Submodule.mem_inf.mpr ⟨hmem2, hmem1⟩))
    -- hence `u ∈ N` and `Φ u = 0`, so `Λ (P u) = 0`, so `P u = 0`, so `u = 0`
    have huN : u ∈ N := by
      rw [hN, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      exact hzero
    have hΦzero : Φ u = 0 := by rw [← hsplit, hzero]
    have hΛzero : Λ (N.orthogonalProjectionOnto u) = 0 := by
      have : (↑(Λ (N.orthogonalProjectionOnto u)) : E) = 0 := hΦzero
      exact_mod_cast this
    have hPzero : N.orthogonalProjectionOnto u = 0 := by
      apply hΛinj
      rw [hΛzero, map_zero]
    have hPu : (↑(N.orthogonalProjectionOnto u) : E) = u := by
      rw [← Submodule.starProjection_apply]
      exact N.starProjection_eq_self_iff.mpr huN
    rw [← hPu, hPzero, Submodule.coe_zero]
  -- the Fredholm alternative makes `1 - S` surjective
  have hnoteig : ¬ Module.End.HasEigenvalue (S : Module.End ℝ E) 1 := by
    rw [Module.End.hasEigenvalue_iff]
    intro hne
    apply hne
    rw [← ker_one_sub_eq_eigenspace S, Submodule.eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hu
    exact hSker u hu
  have hsurj : Function.Surjective (1 - S : E →L[ℝ] E) := by
    rcases hScompact.hasEigenvalue_or_mem_resolventSet (μ := (1 : ℝ)) one_ne_zero with
      he | hr
    · exact absurd he hnoteig
    · have hunit : IsUnit ((1 : E →L[ℝ] E) - S) := by
        have h := spectrum.mem_resolventSet_iff.mp hr
        rwa [map_one] at h
      exact (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).2
  -- yet nothing outside `range Λ` is attained: contradiction
  obtain ⟨u, hu⟩ := hsurj (↑ystar : E)
  have hsplit : (1 - K : E →L[ℝ] E) u = ↑ystar + Φ u := by
    have h1 : (1 - S) u = (1 - K : E →L[ℝ] E) u - Φ u := by
      simp only [hSdef, _root_.sub_apply, one_apply_eq_self,
        _root_.add_apply]
      abel
    rw [h1] at hu
    exact sub_eq_iff_eq_add.mp hu
  have hmem1' : (1 - K : E →L[ℝ] E) u ∈ Nstarᗮ := by
    rw [← hrangeNstar]
    exact ⟨u, rfl⟩
  have hmem2' : (1 - K : E →L[ℝ] E) u ∈ Nstar := by
    rw [hsplit]
    exact Nstar.add_mem (SetLike.coe_mem ystar) (hΦmem u)
  have hzero : (1 - K : E →L[ℝ] E) u = 0 := (Submodule.mem_bot ℝ).mp
    (Nstar.orthogonal_disjoint.le_bot (Submodule.mem_inf.mpr ⟨hmem2', hmem1'⟩))
  have hy : (↑ystar : E) = -(Φ u) := by
    have h2 := hsplit
    rw [hzero] at h2
    exact add_eq_zero_iff_eq_neg.mp h2.symm
  have hΦu : Φ u = ↑(Λ (N.orthogonalProjectionOnto u)) := by
    simp only [hΦdef, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      LinearMap.coe_toContinuousLinearMap']
  have hyrange : ystar ∈ LinearMap.range Λ := by
    refine ⟨-(N.orthogonalProjectionOnto u), ?_⟩
    refine Subtype.coe_injective ?_
    rw [map_neg]
    simp only [Submodule.coe_neg]
    rw [← hΦu, ← hy]
  exact hystar hyrange

/-- **`dim ker(1 - K) = dim ker(1 - K†)`** for a compact operator on a real Hilbert
space (the abstract form of Evans §6.2.3, Theorem 4(ii)): the index of `1 - K` is
zero. Both inequalities are
`finrank_ker_one_sub_adjoint_le`, the reverse one applied to `K†` through Schauder's
theorem and `K†† = K`. -/
theorem finrank_ker_one_sub_adjoint_eq (hK : IsCompactOperator K) :
    Module.finrank ℝ
      (LinearMap.ker ((1 - ContinuousLinearMap.adjoint K : E →L[ℝ] E)).toLinearMap)
      = Module.finrank ℝ (LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap) := by
  refine le_antisymm (finrank_ker_one_sub_adjoint_le hK) ?_
  have h := finrank_ker_one_sub_adjoint_le (isCompactOperator_adjoint hK)
  rwa [ContinuousLinearMap.adjoint_adjoint] at h

/-- The adjoint of (the underlying map of) a continuous linear equivalence is
bijective: the adjoint of the inverse is a two-sided inverse. -/
lemma bijective_adjoint_of_equiv (e : E ≃L[ℝ] E) :
    Function.Bijective (ContinuousLinearMap.adjoint (e : E →L[ℝ] E)) := by
  have h1 : (ContinuousLinearMap.adjoint (e : E →L[ℝ] E)).comp
      (ContinuousLinearMap.adjoint (e.symm : E →L[ℝ] E)) = 1 := by
    rw [← ContinuousLinearMap.adjoint_comp]
    have hcomp : (e.symm : E →L[ℝ] E).comp (e : E →L[ℝ] E) = 1 := by
      ext x
      simp
    rw [hcomp, ContinuousLinearMap.adjoint_one]
  have h2 : (ContinuousLinearMap.adjoint (e.symm : E →L[ℝ] E)).comp
      (ContinuousLinearMap.adjoint (e : E →L[ℝ] E)) = 1 := by
    rw [← ContinuousLinearMap.adjoint_comp]
    have hcomp : (e : E →L[ℝ] E).comp (e.symm : E →L[ℝ] E) = 1 := by
      ext x
      simp
    rw [hcomp, ContinuousLinearMap.adjoint_one]
  have hl : Function.LeftInverse (ContinuousLinearMap.adjoint (e.symm : E →L[ℝ] E))
      (ContinuousLinearMap.adjoint (e : E →L[ℝ] E)) := fun x => by
    rw [← ContinuousLinearMap.comp_apply, h2, one_apply_eq_self]
  have hr : Function.RightInverse (ContinuousLinearMap.adjoint (e.symm : E →L[ℝ] E))
      (ContinuousLinearMap.adjoint (e : E →L[ℝ] E)) := fun x => by
    rw [← ContinuousLinearMap.comp_apply, h1, one_apply_eq_self]
  exact ⟨hl.injective, hr.surjective⟩

/-- **Fredholm alternative** (Evans Appendix D Theorem 5, Guo Theorem VII.4.4) for a compact
operator `K` on a real Hilbert space: the kernel of `1 - K` is finite dimensional, the range of
`1 - K` is closed and is the orthogonal complement of the kernel of `1 - K†`, `1 - K` is
injective exactly when it is surjective, and the kernels of `1 - K` and `1 - K†` have the same
dimension. -/
theorem fredholm_alternative_compact (hK : IsCompactOperator K) :
    FiniteDimensional ℝ (LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap) ∧
    IsClosed (Set.range (1 - K : E →L[ℝ] E)) ∧
    LinearMap.range ((1 - K : E →L[ℝ] E)).toLinearMap
      = (LinearMap.ker ((1 - ContinuousLinearMap.adjoint K : E →L[ℝ] E)).toLinearMap)ᗮ ∧
    (LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap = ⊥ ↔
      LinearMap.range ((1 - K : E →L[ℝ] E)).toLinearMap = ⊤) ∧
    Module.finrank ℝ
        (LinearMap.ker ((1 - ContinuousLinearMap.adjoint K : E →L[ℝ] E)).toLinearMap)
      = Module.finrank ℝ (LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap) := by
  have hfin := finiteDimensional_ker_one_sub hK
  have hcl := isClosed_range_one_sub hK
  have hrange : LinearMap.range ((1 - K : E →L[ℝ] E)).toLinearMap
      = (LinearMap.ker ((1 - ContinuousLinearMap.adjoint K : E →L[ℝ] E)).toLinearMap)ᗮ := by
    rw [range_eq_orthogonal_ker_adjoint _ hcl, adjoint_one_sub]
  have hrank := finrank_ker_one_sub_adjoint_eq hK
  refine ⟨hfin, hcl, hrange, ⟨fun hker => ?_, fun hran => ?_⟩, hrank⟩
  · -- injective implies surjective, through the dichotomy for the eigenvalue `1`
    rcases hK.hasEigenvalue_or_mem_resolventSet (μ := (1 : ℝ)) one_ne_zero with he | hr
    · exfalso
      have h1 : Module.End.eigenspace (K : Module.End ℝ E) 1 ≠ ⊥ := he
      rw [← ker_one_sub_eq_eigenspace] at h1
      exact h1 hker
    · rw [spectrum.mem_resolventSet_iff, map_one] at hr
      obtain ⟨u, hu⟩ := hr
      rw [LinearMap.range_eq_top]
      intro y
      refine ⟨u.inv y, ?_⟩
      have : (1 - K : E →L[ℝ] E) * u.inv = 1 := by rw [← hu, Units.val_inv]
      change ((1 - K : E →L[ℝ] E) * u.inv) y = y
      rw [this, one_apply_eq_self]
  · -- surjective implies injective, through the equality of dimensions
    have h1 : (LinearMap.ker ((1 - ContinuousLinearMap.adjoint K : E →L[ℝ] E)).toLinearMap)ᗮ
        = ⊤ := by rw [← hrange, hran]
    rw [Submodule.orthogonal_eq_top_iff] at h1
    rw [h1, finrank_bot] at hrank
    exact Submodule.finrank_eq_zero.mp hrank.symm

/-- **Fredholm dichotomy** (Evans Appendix D Theorem 5, the remark following it; Guo Theorem
VII.4.4): either `(1 - K) u = h` has exactly one solution for every `h`, or the homogeneous
equation has a nonzero solution. -/
theorem fredholm_dichotomy_compact (hK : IsCompactOperator K) :
    (∀ h : E, ∃! u : E, (1 - K : E →L[ℝ] E) u = h)
      ∨ ∃ u : E, u ≠ 0 ∧ (1 - K : E →L[ℝ] E) u = 0 := by
  obtain ⟨-, -, -, hiff, -⟩ := fredholm_alternative_compact hK
  by_cases hker : LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap = ⊥
  · left
    have hran := hiff.mp hker
    intro h
    obtain ⟨u, hu⟩ := LinearMap.range_eq_top.mp hran h
    have hu0 : (1 - K : E →L[ℝ] E) u = h := hu
    refine ⟨u, hu0, fun u' hu' => ?_⟩
    have hu1 : (1 - K : E →L[ℝ] E) u' = h := hu'
    have hmem : u' - u ∈ LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub]
      change (1 - K : E →L[ℝ] E) u' - (1 - K : E →L[ℝ] E) u = 0
      rw [hu1, hu0, sub_self]
    rw [hker, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hmem
  · right
    obtain ⟨u, hu, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    exact ⟨u, hne, hu⟩

end RieszTheory

variable {d : ℕ}

namespace FullEllipticOp

variable (Op : FullEllipticOp d) (Ω : Set (EuclideanSpace ℝ (Fin d)))

/-- The space `N` of weak solutions of the homogeneous problem `Lu = 0`: the kernel of
the Riesz representative `opA` of the full divergence form. -/
def solSpace : Submodule ℝ (H01 Ω) := LinearMap.ker (Op.opA Ω).toLinearMap

/-- Membership in `solSpace` is exactly being a weak solution of the homogeneous
problem: `B[u, v] = 0` against every `v ∈ H₀¹(Ω)`. The proofs below reach `solSpace`
through `solSpace_eq_eigenspace` instead. -/
lemma mem_solSpace_iff (u : H01 Ω) :
    u ∈ Op.solSpace Ω ↔ ∀ v : H01 Ω, Op.fullBilin Ω u v = 0 := by
  rw [solSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro hu v
    rw [← Op.inner_opA Ω u v, hu, inner_zero_left]
  · intro hu
    refine ext_inner_right (𝕜 := ℝ) (fun v => ?_)
    rw [Op.inner_opA Ω u v, hu v, inner_zero_left]

/-- The homogeneous solution space is the eigenspace of the compact part `opK` at the
eigenvalue `1`: since `opA = opE ∘ (1 - opK)` with `opE` an equivalence,
`opA u = 0 ↔ opK u = u`. -/
lemma solSpace_eq_eigenspace :
    Op.solSpace Ω = Module.End.eigenspace (Op.opK Ω).toLinearMap 1 := by
  ext u
  rw [solSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    Module.End.mem_eigenspace_iff, one_smul]
  have hfac : Op.opA Ω u = (Op.opE Ω) ((1 - Op.opK Ω) u) := by
    rw [Op.opA_factor Ω]; rfl
  constructor
  · intro hu
    have h0 : (1 - Op.opK Ω) u = 0 := by
      apply (Op.opE Ω).injective
      rw [← hfac, hu, map_zero]
    rw [_root_.sub_apply, one_apply_eq_self, sub_eq_zero] at h0
    exact h0.symm
  · intro hu
    have h0 : (1 - Op.opK Ω) u = 0 := by
      rw [_root_.sub_apply, one_apply_eq_self,
        show Op.opK Ω u = u from hu, sub_self]
    rw [hfac, h0, map_zero]

/-- **Finite-dimensionality of the homogeneous solution space** (the finite-dimensionality
half of Evans §6.2.3, Theorem 4(ii)).
Under the Rellich-Kondrachov input (`opK` compact), the space of weak solutions of the
homogeneous problem `Lu = 0` is finite-dimensional: it is the eigenspace of the compact
operator `opK` at the nonzero eigenvalue `1`, and Riesz theory makes such eigenspaces
finite-dimensional.

Terminal result of the library, stated in the manuscript. Nothing else consumes it. -/
theorem finiteDimensional_solSpace (hK : IsCompactOperator (Op.opK Ω)) :
    FiniteDimensional ℝ (Op.solSpace Ω) := by
  rw [solSpace_eq_eigenspace]
  exact ContinuousLinearMap.finite_dimensional_eigenspace hK 1 one_ne_zero

/-- **Closed range of the elliptic operator** (towards Evans §6.2.3, Theorem
4(ii)-(iii)). Under
the Rellich-Kondrachov input the range of `opA` (the set of Riesz representatives of
solvable right-hand sides) is closed: `opA = opE ∘ (1 - opK)` with `opE` a
homeomorphism, and `1 - opK` has closed range by Riesz theory. This is the geometric
input for the solvability criterion `Lu = f solvable ↔ f ⊥ N*`. -/
theorem isClosed_range_opA (hK : IsCompactOperator (Op.opK Ω)) :
    IsClosed (Set.range (Op.opA Ω)) := by
  have h1 : IsClosed (Set.range (1 - Op.opK Ω : H01 Ω →L[ℝ] H01 Ω)) :=
    isClosed_range_one_sub hK
  have h2 : Set.range (Op.opA Ω)
      = (Op.opE Ω) '' Set.range (1 - Op.opK Ω : H01 Ω →L[ℝ] H01 Ω) := by
    rw [Op.opA_factor Ω, ContinuousLinearMap.coe_comp, Set.range_comp]
    rfl
  rw [h2]
  exact (Op.opE Ω).toHomeomorph.isClosedMap _ h1

/-- The **adjoint solution space** `N*`: the kernel of the Hilbert adjoint of `opA`,
which is exactly the space of weak solutions of the **transpose problem**
`B[v, u] = 0` for all `v` (the adjoint bilinear form and adjoint problem defined ahead
of Evans §6.2.3, Theorem 4: the adjoint problem is the transpose form, with no
differentiability demanded of the coefficients). -/
def solSpaceStar : Submodule ℝ (H01 Ω) :=
  LinearMap.ker (ContinuousLinearMap.adjoint (Op.opA Ω)).toLinearMap

/-- Membership in `solSpaceStar` is exactly being a weak solution of the transpose
problem: `B[v, u] = 0` against every `v ∈ H₀¹(Ω)`, the transpose counterpart of
`mem_solSpace_iff`. -/
lemma mem_solSpaceStar_iff (u : H01 Ω) :
    u ∈ Op.solSpaceStar Ω ↔ ∀ v : H01 Ω, Op.fullBilin Ω v u = 0 := by
  rw [solSpaceStar, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro hu v
    rw [← Op.inner_opA Ω v u, ← ContinuousLinearMap.adjoint_inner_right, hu,
      inner_zero_right]
  · intro hu
    refine ext_inner_right (𝕜 := ℝ) (fun v => ?_)
    rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm,
      Op.inner_opA Ω v u]
    exact hu v

/-- **Solvability criterion** (Evans §6.2.3, Theorem 4(iii)). Under the
Rellich-Kondrachov input, the weak problem `Lu = f` is solvable exactly when `f`
annihilates the adjoint solution space: `∃u ∀v, B[u, v] = f(v)` iff `f(w) = 0` for
every weak solution `w` of the transpose problem `B[v, w] = 0`. The proof is closed
range (`isClosed_range_opA`) plus the Hilbert-space duality
`range A = (ker A†)ᗮ`. -/
theorem solvable_iff_orthogonal_solSpaceStar (hK : IsCompactOperator (Op.opK Ω))
    (f : H01 Ω →L[ℝ] ℝ) :
    (∃ u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v)
      ↔ ∀ w ∈ Op.solSpaceStar Ω, f w = 0 := by
  set g : H01 Ω := (InnerProductSpace.toDual ℝ (H01 Ω)).symm f with hg
  have hgrep : ∀ v : H01 Ω, ⟪g, v⟫ = f v := fun v => InnerProductSpace.toDual_symm_apply
  have hiff : (∃ u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v)
      ↔ g ∈ LinearMap.range (Op.opA Ω).toLinearMap := by
    rw [LinearMap.mem_range]
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨u, ?_⟩
      change Op.opA Ω u = g
      refine ext_inner_right (𝕜 := ℝ) (fun v => ?_)
      rw [Op.inner_opA Ω u v, hu v, hgrep v]
    · rintro ⟨u, hu⟩
      have hu' : Op.opA Ω u = g := hu
      exact ⟨u, fun v => by rw [← Op.inner_opA Ω u v, hu', hgrep v]⟩
  rw [hiff, range_eq_orthogonal_ker_adjoint _ (Op.isClosed_range_opA Ω hK),
    Submodule.mem_orthogonal]
  constructor
  · intro h w hw
    rw [← hgrep w, real_inner_comm]
    exact h w hw
  · intro h w hw
    rw [real_inner_comm, hgrep w]
    exact h w hw

/-- **`dim N = dim N*` for the elliptic problem** (Evans §6.2.3, Theorem 4(ii)). The
space of weak
solutions of the homogeneous problem and the space of weak solutions of the transpose
problem have the same (finite) dimension. The factorisation `opA = opE ∘ (1 - opK)`
maps `solSpaceStar = ker(opA†)` onto `ker(1 - opK†)` along the bijection `(opE)†`,
and the abstract index theorem `finrank_ker_one_sub_adjoint_eq` applies.

Terminal result of the library, stated in the manuscript. Nothing else consumes it. -/
theorem finrank_solSpaceStar_eq_finrank_solSpace (hK : IsCompactOperator (Op.opK Ω)) :
    Module.finrank ℝ (Op.solSpaceStar Ω) = Module.finrank ℝ (Op.solSpace Ω) := by
  let T : H01 Ω →L[ℝ] H01 Ω :=
    ContinuousLinearMap.adjoint (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω)
  set Q := LinearMap.ker ((1 - ContinuousLinearMap.adjoint (Op.opK Ω) :
    H01 Ω →L[ℝ] H01 Ω)).toLinearMap with hQdef
  -- `opA† = (1 - opK†) ∘ T`, then pointwise
  have hadj : ContinuousLinearMap.adjoint (Op.opA Ω)
      = ((1 : H01 Ω →L[ℝ] H01 Ω) - ContinuousLinearMap.adjoint (Op.opK Ω)).comp T := by
    calc
      ContinuousLinearMap.adjoint (Op.opA Ω) =
          ContinuousLinearMap.adjoint
            ((Op.opE Ω : H01 Ω →L[ℝ] H01 Ω).comp (1 - Op.opK Ω)) :=
        congrArg ContinuousLinearMap.adjoint (Op.opA_factor Ω)
      _ = (ContinuousLinearMap.adjoint (1 - Op.opK Ω)).comp T :=
        ContinuousLinearMap.adjoint_comp _ _
      _ = ((1 : H01 Ω →L[ℝ] H01 Ω) -
          ContinuousLinearMap.adjoint (Op.opK Ω)).comp T :=
        congrArg (fun L : H01 Ω →L[ℝ] H01 Ω => L.comp T) (adjoint_one_sub _)
  have hadjpt : ∀ u : H01 Ω, ContinuousLinearMap.adjoint (Op.opA Ω) u
      = ((1 : H01 Ω →L[ℝ] H01 Ω) - ContinuousLinearMap.adjoint (Op.opK Ω)) (T u) := by
    intro u
    exact congrArg (fun L : H01 Ω →L[ℝ] H01 Ω => L u) hadj
  have hTbij : Function.Bijective T := bijective_adjoint_of_equiv (Op.opE Ω)
  -- `T` restricts to a linear equivalence `solSpaceStar ≃ ker(1 - opK†)`
  have hrestrict : ∀ u : H01 Ω, u ∈ Op.solSpaceStar Ω → T u ∈ Q := by
    intro u hu
    rw [solSpaceStar, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hu
    rw [hQdef, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ← hadjpt u]
    exact hu
  let Trest : Op.solSpaceStar Ω →ₗ[ℝ] Q := T.toLinearMap.restrict hrestrict
  have hinj : Function.Injective Trest := by
    intro a b hab
    apply Subtype.coe_injective
    apply hTbij.1
    have h := congrArg (Subtype.val) hab
    change T (a : H01 Ω) = T (b : H01 Ω) at h
    exact h
  have hsurj : Function.Surjective Trest := by
    intro w
    obtain ⟨u, hu⟩ := hTbij.2 (↑w : H01 Ω)
    have humem : u ∈ Op.solSpaceStar Ω := by
      rw [solSpaceStar, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hadjpt u, hu]
      have hw : ((1 - ContinuousLinearMap.adjoint (Op.opK Ω) : H01 Ω →L[ℝ] H01 Ω))
          (↑w : H01 Ω) = 0 := LinearMap.mem_ker.mp w.2
      exact hw
    refine ⟨⟨u, humem⟩, ?_⟩
    apply Subtype.coe_injective
    change T u = (w : H01 Ω)
    exact hu
  have heq : Module.finrank ℝ (Op.solSpaceStar Ω) = Module.finrank ℝ Q :=
    (LinearEquiv.ofBijective Trest ⟨hinj, hsurj⟩).finrank_eq
  have hNs : LinearMap.ker ((1 - Op.opK Ω : H01 Ω →L[ℝ] H01 Ω)).toLinearMap
      = Op.solSpace Ω := by
    rw [ker_one_sub_eq_eigenspace, ← Op.solSpace_eq_eigenspace Ω]
  rw [heq, hQdef, finrank_ker_one_sub_adjoint_eq hK, hNs]

end FullEllipticOp

end EllipticPdes.Sobolev
