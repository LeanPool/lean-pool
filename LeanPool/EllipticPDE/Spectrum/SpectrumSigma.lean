/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Fredholm.FredholmComplete
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension


/-!
# Spectrum of compact operators and Existence III

Two layers.

**Generic** (Evans Appendix D.5, Theorem 6: the spectrum of a compact operator `K` on a
real Hilbert space): `0 ∈ σ(K)` when the space is infinite-dimensional; away from zero
the spectrum consists of eigenvalues (mathlib's Fredholm alternative); and the
eigenvalues cannot accumulate away from zero: for every `δ > 0` only finitely many
eigenvalues have `|μ| ≥ δ`, so `σ(K) \ {0}` is countable. The accumulation argument is
the classical eigenvector chain: distinct eigenvalues give a strictly increasing chain
of spans `Eₙ`, Hilbert geometry provides unit vectors `uₙ ∈ Eₙ₊₁ ∩ Eₙᗮ`, and
`(μₙ - K)Eₙ₊₁ ⊆ Eₙ` forces `‖K(uₙ/μₙ) - K(uₘ/μₘ)‖ ≥ 1` for `m < n`, contradicting
the compactness of `K` on the bounded sequence `uₙ/μₙ`.

**Elliptic** (`Existence III`, obtained by parametrising the Fredholm alternative of
Evans §6.2.3 by the shift `λ` and invoking the spectral theorem of Evans Appendix D.5):
the set `Σ = {λ : γ/(γ+λ) is an eigenvalue of opK}` is countable with finite
intersections with every `Set.Iic C` (so an infinite `Σ` is a sequence increasing to
`+∞`), and `λ ∉ Σ` holds exactly when the weak problem `Lu = λu + f` is uniquely
solvable for every right-hand side. The reduction is the `opK` factorisation of
`Fredholm.lean`, shifted: `opAlam = opE ∘ (1 - ((γ+λ)/γ)·opK)`. Eigenvalues of `opK`
are positive (coercivity of the shifted form), which bounds `Σ` inside `(-γ, ∞)`.
-/

@[expose] public section

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

/-! ### Spectrum of a compact operator (Evans Appendix D.5, Theorem 6) -/

section CompactSpectrum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {K : E →L[ℝ] E}

omit [CompleteSpace E] in
/-- **Eigenvalues of a compact operator do not accumulate away from zero**: for every
`δ > 0` there are only finitely many eigenvalues `μ` with `δ ≤ |μ|`. The classical
eigenvector-chain argument, with the Riesz lemma replaced by Hilbert orthogonality. -/
theorem finite_setOf_hasEigenvalue_abs_ge (hK : IsCompactOperator K)
    {δ : ℝ} (hδ : 0 < δ) :
    {μ : ℝ | Module.End.HasEigenvalue (K.toLinearMap) μ ∧ δ ≤ |μ|}.Finite := by
  by_contra hcon
  have hinf : {μ : ℝ | Module.End.HasEigenvalue (K.toLinearMap) μ ∧ δ ≤ |μ|}.Infinite :=
    hcon
  set emb := hinf.natEmbedding with hembdef
  set μs : ℕ → ℝ := fun n => (emb n : ℝ) with hμsdef
  have hμinj : Function.Injective μs := fun a b hab =>
    emb.injective (Subtype.coe_injective hab)
  have hμprop : ∀ n, Module.End.HasEigenvalue (K.toLinearMap) (μs n) ∧ δ ≤ |μs n| :=
    fun n => (emb n).2
  have hμne : ∀ n, μs n ≠ 0 := by
    intro n h0
    have h := (hμprop n).2
    rw [h0, abs_zero] at h
    linarith
  -- eigenvectors and their linear independence
  have hvec : ∀ n : ℕ, ∃ v : E, Module.End.HasEigenvector (K.toLinearMap) (μs n) v :=
    fun n => (hμprop n).1.exists_hasEigenvector
  choose e he using hvec
  have hli : LinearIndependent ℝ e :=
    Module.End.eigenvectors_linearIndependent' (K.toLinearMap) μs hμinj e he
  have hKe : ∀ i : ℕ, K (e i) = μs i • e i := fun i =>
    Module.End.mem_eigenspace_iff.mp (he i).1
  -- the increasing chain of spans
  set Espan : ℕ → Submodule ℝ E := fun n => Submodule.span ℝ (e '' Set.Iio n) with hEdef
  have hEmono : ∀ {m n : ℕ}, m ≤ n → Espan m ≤ Espan n := fun {m n} hmn =>
    Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hmn))
  have heMem : ∀ {i n : ℕ}, i < n → e i ∈ Espan n := fun {i n} hin =>
    Submodule.subset_span ⟨i, hin, rfl⟩
  have heNot : ∀ n : ℕ, e n ∉ Espan n := fun n =>
    hli.notMem_span_image (by simp)
  -- `K` preserves each `Espan n`
  have hKmap : ∀ n : ℕ, ∀ x ∈ Espan n, K x ∈ Espan n := by
    intro n
    have h1 : e '' Set.Iio n ⊆ (Submodule.comap K.toLinearMap (Espan n) : Set E) := by
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      change K (e i) ∈ Espan n
      rw [hKe i]
      exact (Espan n).smul_mem _ (heMem hi)
    intro x hx
    exact (Submodule.span_le.mpr h1) hx
  -- `(μₙ - K)` drops `Espan (n+1)` into `Espan n`
  have hshift : ∀ n : ℕ, ∀ x ∈ Espan (n + 1), μs n • x - K x ∈ Espan n := by
    intro n
    set L : E →ₗ[ℝ] E := μs n • LinearMap.id - K.toLinearMap with hLdef
    have h1 : e '' Set.Iio (n + 1) ⊆ (Submodule.comap L (Espan n) : Set E) := by
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have happ : L (e i) = (μs n - μs i) • e i := by
        simp only [hLdef, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
          ContinuousLinearMap.coe_coe]
        rw [hKe i, sub_smul]
      rw [happ]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact (Espan n).smul_mem _ (heMem h)
      · subst h
        rw [sub_self, zero_smul]
        exact Submodule.zero_mem _
    intro x hx
    have h3 := (Submodule.span_le.mpr h1) hx
    rw [Submodule.mem_comap] at h3
    simpa [hLdef, LinearMap.sub_apply, LinearMap.smul_apply] using h3
  -- unit vectors in `Espan (n+1)` orthogonal to `Espan n`
  have hunit : ∀ n : ℕ, ∃ u : E, u ∈ Espan (n + 1) ∧ u ∈ (Espan n)ᗮ ∧ ‖u‖ = 1 := by
    intro n
    have : FiniteDimensional ℝ (Espan n) :=
      FiniteDimensional.span_of_finite ℝ ((Set.finite_Iio n).image e)
    set w : E := e n - (Espan n).starProjection (e n) with hwdef
    have hw_orth : w ∈ (Espan n)ᗮ := (Espan n).sub_starProjection_mem_orthogonal (e n)
    have hproj_mem : (Espan n).starProjection (e n) ∈ Espan n := by
      rw [Submodule.starProjection_apply]
      exact SetLike.coe_mem _
    have hw_mem : w ∈ Espan (n + 1) :=
      Submodule.sub_mem _ (heMem (Nat.lt_succ_self n)) (hEmono (Nat.le_succ n) hproj_mem)
    have hw0 : w ≠ 0 := by
      intro h0
      apply heNot n
      have h1 : e n = (Espan n).starProjection (e n) := by
        rwa [hwdef, sub_eq_zero] at h0
      rw [h1]
      exact hproj_mem
    have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    refine ⟨‖w‖⁻¹ • w, Submodule.smul_mem _ _ hw_mem, Submodule.smul_mem _ _ hw_orth, ?_⟩
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwn]
  choose u hu_mem hu_orth hu_norm using hunit
  -- the bounded sequence `vₙ = uₙ/μₙ` and the unit separation of its `K`-image
  set v : ℕ → E := fun n => (μs n)⁻¹ • u n with hvdef
  have hsep : ∀ m n : ℕ, m < n → 1 ≤ ‖K (v n) - K (v m)‖ := by
    intro m n hmn
    have hKvn : K (v n) = u n - (μs n)⁻¹ • (μs n • u n - K (u n)) := by
      rw [hvdef]
      simp only [map_smul]
      rw [smul_sub, smul_smul, inv_mul_cancel₀ (hμne n), one_smul]
      abel
    set wn : E := (μs n)⁻¹ • (μs n • u n - K (u n)) with hwndef
    have hwn_mem : wn ∈ Espan n :=
      Submodule.smul_mem _ _ (hshift n (u n) (hu_mem n))
    have hKvm_mem : K (v m) ∈ Espan n := by
      have h1 : K (v m) ∈ Espan (m + 1) := by
        rw [hvdef]
        simp only [map_smul]
        exact Submodule.smul_mem _ _ (hKmap (m + 1) (u m) (hu_mem m))
      exact hEmono (Nat.succ_le_of_lt hmn) h1
    set z : E := wn + K (v m) with hzdef
    have hz_mem : z ∈ Espan n := Submodule.add_mem _ hwn_mem hKvm_mem
    have hdiff : K (v n) - K (v m) = u n - z := by
      rw [hKvn, hzdef, hwndef]
      abel
    have horth : ⟪u n, z⟫ = 0 :=
      (Submodule.mem_orthogonal' (Espan n) (u n)).mp (hu_orth n) z hz_mem
    have hsq : ‖u n - z‖ ^ 2 = 1 + ‖z‖ ^ 2 := by
      rw [norm_sub_sq_real, horth, hu_norm n]
      ring
    rw [hdiff]
    nlinarith [norm_nonneg (u n - z), sq_nonneg ‖z‖, hsq]
  -- compactness extracts a Cauchy subsequence of `K vₙ`: contradiction
  have hvball : ∀ n : ℕ, v n ∈ Metric.closedBall (0 : E) δ⁻¹ := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right, hvdef]
    simp only [norm_smul, norm_inv, Real.norm_eq_abs]
    rw [hu_norm n, mul_one]
    exact inv_anti₀ hδ (hμprop n).2
  have hK' : IsCompactOperator K.toLinearMap := hK
  have hcpt : IsCompact (closure (K.toLinearMap '' Metric.closedBall 0 δ⁻¹)) :=
    hK'.isCompact_closure_image_closedBall δ⁻¹
  have hmem : ∀ n : ℕ, K (v n) ∈ closure (K.toLinearMap '' Metric.closedBall 0 δ⁻¹) :=
    fun n => subset_closure ⟨v n, hvball n, rfl⟩
  obtain ⟨z₀, -, φ, hφ, hzlim⟩ := hcpt.tendsto_subseq hmem
  have hcauchy : CauchySeq (fun k => K (v (φ k))) := hzlim.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨krep, hkrep⟩ := hcauchy 1 one_pos
  have hlt : φ krep < φ (krep + 1) := hφ (Nat.lt_succ_self krep)
  have h1 := hkrep (krep + 1) (Nat.le_succ krep) krep (le_refl krep)
  rw [dist_eq_norm] at h1
  exact absurd h1 (not_lt.mpr (hsep (φ krep) (φ (krep + 1)) hlt))

omit [CompleteSpace E] in
/-- The nonzero eigenvalues of a compact operator form a countable set: the union of
the finite slices `{δ ≤ |μ|}` over `δ = 1/(n+1)`. -/
theorem countable_setOf_hasEigenvalue_ne_zero (hK : IsCompactOperator K) :
    {μ : ℝ | Module.End.HasEigenvalue (K.toLinearMap) μ ∧ μ ≠ 0}.Countable := by
  have hsub : {μ : ℝ | Module.End.HasEigenvalue (K.toLinearMap) μ ∧ μ ≠ 0}
      ⊆ ⋃ n : ℕ, {μ : ℝ | Module.End.HasEigenvalue (K.toLinearMap) μ
          ∧ 1 / (n + 1) ≤ |μ|} := by
    rintro μ ⟨hμ, hμ0⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr hμ0)
    exact Set.mem_iUnion.mpr ⟨n, hμ, hn.le⟩
  exact Set.Countable.mono hsub (Set.countable_iUnion (fun n =>
    (finite_setOf_hasEigenvalue_abs_ge hK (by positivity)).countable))

omit [CompleteSpace E] in
/-- `0` lies in the (real) spectrum of a compact operator on an infinite-dimensional
space: an inverse would make the identity compact (Evans Appendix D.5, Theorem 6(i)). -/
theorem zero_mem_spectrum_of_compact (hK : IsCompactOperator K)
    (hinf : ¬ FiniteDimensional ℝ E) : (0 : ℝ) ∈ spectrum ℝ K := by
  rw [spectrum.mem_iff]
  intro hunit
  rw [map_zero, zero_sub] at hunit
  have hKunit : IsUnit K := by
    have h := hunit.neg
    rwa [neg_neg] at h
  obtain ⟨w, hw⟩ := hKunit
  apply hinf
  have hinv : (↑w⁻¹ : E →L[ℝ] E) * K = 1 := by
    rw [← hw]
    exact w.inv_mul
  have hid : IsCompactOperator ((↑w⁻¹ : E →L[ℝ] E) ∘ (K : E → E)) := hK.clm_comp _
  have hone : IsCompactOperator ⇑((↑w⁻¹ : E →L[ℝ] E) * K) := hid
  rw [hinv] at hone
  rw [ContinuousLinearMap.one_def, ContinuousLinearMap.coe_id'] at hone
  rw [← isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ)]
  exact hone

/-- Away from zero the spectrum of a compact operator consists exactly of the
eigenvalues (Evans Appendix D.5, Theorem 6(ii)), mathlib's Fredholm alternative as a
set identity. -/
theorem spectrum_diff_eq_eigenvalues (hK : IsCompactOperator K) :
    spectrum ℝ K \ {0}
      = {μ : ℝ | Module.End.HasEigenvalue (K.toLinearMap) μ} \ {0} := by
  ext μ
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hmem, h0⟩
    exact ⟨(hK.hasEigenvalue_iff_mem_spectrum h0).mpr hmem, h0⟩
  · rintro ⟨heig, h0⟩
    exact ⟨(hK.hasEigenvalue_iff_mem_spectrum h0).mp heig, h0⟩

/-- **Spectrum of a compact operator (Evans Appendix D.5, Theorem 6).** On an
infinite-dimensional real Hilbert space, a compact operator `K` has `0` in its real
spectrum; away from zero the spectrum consists exactly of the eigenvalues; the nonzero
spectrum is countable; and only finitely many spectral points have `|μ| ≥ δ` for each
`δ > 0`, so an enumeration of the nonzero spectrum converges to `0`.

Terminal result of the library, stated in the manuscript. Nothing else consumes it. -/
theorem spectrum_compact_operator (hK : IsCompactOperator K)
    (hinf : ¬ FiniteDimensional ℝ E) :
    (0 : ℝ) ∈ spectrum ℝ K
    ∧ spectrum ℝ K \ {0}
        = {μ : ℝ | Module.End.HasEigenvalue (K.toLinearMap) μ} \ {0}
    ∧ (spectrum ℝ K \ {0}).Countable
    ∧ ∀ δ : ℝ, 0 < δ → {μ ∈ spectrum ℝ K | δ ≤ |μ|}.Finite := by
  refine ⟨zero_mem_spectrum_of_compact hK hinf, spectrum_diff_eq_eigenvalues hK, ?_, ?_⟩
  · have h1 : spectrum ℝ K \ {0}
        ⊆ {μ : ℝ | Module.End.HasEigenvalue (K.toLinearMap) μ ∧ μ ≠ 0} := by
      rw [spectrum_diff_eq_eigenvalues hK]
      rintro μ ⟨hμ, h0⟩
      exact ⟨hμ, h0⟩
    exact Set.Countable.mono h1 (countable_setOf_hasEigenvalue_ne_zero hK)
  · intro δ hδ
    have h1 : {μ ∈ spectrum ℝ K | δ ≤ |μ|}
        ⊆ {μ : ℝ | Module.End.HasEigenvalue (K.toLinearMap) μ ∧ δ ≤ |μ|} := by
      rintro μ ⟨hmem, habs⟩
      have h0 : μ ≠ 0 := by
        intro h
        rw [h, abs_zero] at habs
        linarith
      exact ⟨(hK.hasEigenvalue_iff_mem_spectrum h0).mpr hmem, habs⟩
    exact (finite_setOf_hasEigenvalue_abs_ge hK hδ).subset h1

end CompactSpectrum

/-! ### Existence III for the elliptic problem -/

namespace FullEllipticOp

variable {d : ℕ} (Op : FullEllipticOp d) (Ω : Set (EuclideanSpace ℝ (Fin d)))

/-- The Gårding shift constant `γ` is strictly positive. -/
lemma gardingγ_pos : 0 < Op.gardingγ := by
  have h1 := Op.lam_pos
  have h2 := Op.Csup_nonneg
  have h3 : (0 : ℝ) ≤ (d : ℝ) * Op.Bsup ^ 2 / (2 * Op.lam) :=
    div_nonneg (by positivity) (by linarith)
  unfold gardingγ
  linarith

/-- **Set `Σ` of Existence III**: the real `λ` for which `γ/(γ+λ)` is an
eigenvalue of the compact part `opK` of the reduction, equivalently (see
`notMem_sigmaSet_iff_solvable`), the `λ` for which the weak problem `Lu = λu + f`
fails to be uniquely solvable for every right-hand side. -/
def sigmaSet : Set ℝ :=
  {lam : ℝ | Op.gardingγ + lam ≠ 0
    ∧ Module.End.HasEigenvalue (Op.opK Ω).toLinearMap
        (Op.gardingγ / (Op.gardingγ + lam))}

/-- Eigenvalues of `opK` are positive: pairing the eigenvalue relation against the
eigenvector gives `μ B_γ[x,x] = γ ‖x₀‖²` with `B_γ[x,x] > 0` by shifted coercivity. -/
lemma opK_eigenvalue_pos {μ : ℝ}
    (hμ : Module.End.HasEigenvalue (Op.opK Ω).toLinearMap μ) (hμ0 : μ ≠ 0) : 0 < μ := by
  obtain ⟨x, hx_mem, hx_ne⟩ := hμ.exists_hasEigenvector
  have hKx : Op.opK Ω x = μ • x := by
    simpa using Module.End.mem_eigenspace_iff.mp hx_mem
  -- `opE (opK x) = γ • opT x`
  have hEK : (Op.opE Ω) (Op.opK Ω x) = Op.gardingγ • opT Ω x := by
    rw [opK]
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, map_smul, ContinuousLinearEquiv.apply_symm_apply]
  -- pair against `x`
  have hinner : μ * Op.shiftedBilin Ω Op.gardingγ x x
      = Op.gardingγ * zerothForm Ω x x := by
    calc μ * Op.shiftedBilin Ω Op.gardingγ x x
        = μ * ⟪(Op.opE Ω) x, x⟫ := by rw [Op.inner_opE Ω]
      _ = ⟪μ • (Op.opE Ω) x, x⟫ := (real_inner_smul_left _ _ _).symm
      _ = ⟪(Op.opE Ω) (μ • x), x⟫ := by rw [map_smul]
      _ = ⟪(Op.opE Ω) (Op.opK Ω x), x⟫ := by rw [hKx]
      _ = ⟪Op.gardingγ • opT Ω x, x⟫ := by rw [hEK]
      _ = Op.gardingγ * ⟪opT Ω x, x⟫ := real_inner_smul_left (opT Ω x) x Op.gardingγ
      _ = Op.gardingγ * zerothForm Ω x x := by rw [inner_opT Ω]
  obtain ⟨c, hc, hcoer⟩ := Op.shiftedBilin_coercive Ω (le_refl Op.gardingγ)
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
  have hBpos : 0 < Op.shiftedBilin Ω Op.gardingγ x x := by
    have h2 : 0 < c * ‖x‖ * ‖x‖ := by positivity
    exact lt_of_lt_of_le h2 (hcoer x)
  have hn0 : 0 ≤ zerothForm Ω x x := by
    rw [zerothForm_apply]
    exact real_inner_self_nonneg
  have hγ := Op.gardingγ_pos
  have hμnn : 0 ≤ μ := by
    by_contra hneg
    push Not at hneg
    have hlt : μ * Op.shiftedBilin Ω Op.gardingγ x x < 0 :=
      mul_neg_of_neg_of_pos hneg hBpos
    have hge : 0 ≤ Op.gardingγ * zerothForm Ω x x :=
      mul_nonneg hγ.le hn0
    linarith [hinner]
  exact lt_of_le_of_ne hμnn (Ne.symm hμ0)

/-- The Riesz operator of the `λ`-shifted weak problem: `⟪opAlam u, v⟫ = B[u,v] - λ⟨u₀,v₀⟩`. -/
def opAlam (lam : ℝ) : H01 Ω →L[ℝ] H01 Ω :=
  (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω) - (Op.gardingγ + lam) • opT Ω

/-- Riesz identity: `⟪Op.opAlam Ω lam u, v⟫ = B[u, v] - lam · zerothForm Ω u v`. -/
lemma inner_opAlam (lam : ℝ) (u v : H01 Ω) :
    ⟪Op.opAlam Ω lam u, v⟫ = Op.fullBilin Ω u v - lam * zerothForm Ω u v := by
  rw [opAlam, _root_.sub_apply, _root_.smul_apply,
    inner_sub_left, real_inner_smul_left, ContinuousLinearEquiv.coe_coe, Op.inner_opE Ω,
    inner_opT Ω, Op.shiftedBilin_apply, zerothForm_apply]
  ring

/-- The factorisation `opAlam = opE ∘ (1 - ((γ+λ)/γ)·opK)` of the `λ`-shifted problem. -/
lemma opAlam_factor (lam : ℝ) :
    Op.opAlam Ω lam = (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω).comp
      ((1 : H01 Ω →L[ℝ] H01 Ω)
        - ((Op.gardingγ + lam) / Op.gardingγ) • Op.opK Ω) := by
  have hγ := Op.gardingγ_pos
  refine ContinuousLinearMap.ext (fun u => ?_)
  simp only [opAlam, _root_.sub_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, one_apply_eq_self, map_sub, map_smul, opK,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  rw [smul_smul, div_mul_cancel₀ _ hγ.ne']

/-- The Riesz dictionary for the `λ`-shifted problem: `u` weakly solves
`B[u,v] = λ⟨u₀,v₀⟩ + f(v)` exactly when `opAlam u` is the Riesz representative of `f`. -/
lemma opAlam_solves_iff (lam : ℝ) (f : H01 Ω →L[ℝ] ℝ) (u : H01 Ω) :
    (∀ v : H01 Ω, Op.fullBilin Ω u v = lam * zerothForm Ω u v + f v)
      ↔ Op.opAlam Ω lam u = (InnerProductSpace.toDual ℝ (H01 Ω)).symm f := by
  have hgrep : ∀ v : H01 Ω, ⟪(InnerProductSpace.toDual ℝ (H01 Ω)).symm f, v⟫ = f v :=
    fun v => InnerProductSpace.toDual_symm_apply
  constructor
  · intro hu
    refine ext_inner_right (𝕜 := ℝ) (fun v => ?_)
    rw [Op.inner_opAlam Ω, hu v, hgrep v]
    ring
  · intro hu v
    have h1 := Op.inner_opAlam Ω lam u v
    rw [hu, hgrep v] at h1
    linarith [h1]

/-- The `λ`-shifted Riesz operator is bijective off `Σ`. -/
lemma opAlam_bijective_of_notMem (hK : IsCompactOperator (Op.opK Ω)) {lam : ℝ}
    (hlam : lam ∉ Op.sigmaSet Ω) : Function.Bijective (Op.opAlam Ω lam) := by
  have hγ := Op.gardingγ_pos
  by_cases hcase : Op.gardingγ + lam = 0
  · -- `λ = -γ`: the problem is the coercive shifted one, `opAlam = opE`
    have h1 : Op.opAlam Ω lam = (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω) := by
      rw [opAlam, hcase]
      module
    rw [h1]
    simpa using (Op.opE Ω).bijective
  · -- otherwise: the Fredholm alternative at `μ = γ/(γ+λ) ≠ 0`
    set μ : ℝ := Op.gardingγ / (Op.gardingγ + lam) with hμdef
    have hμ0 : μ ≠ 0 := div_ne_zero hγ.ne' hcase
    have hnoteig : ¬ Module.End.HasEigenvalue (Op.opK Ω).toLinearMap μ := by
      intro h
      exact hlam ⟨hcase, h⟩
    rcases hK.hasEigenvalue_or_mem_resolventSet (μ := μ) hμ0 with he | hr
    · exact absurd he hnoteig
    · have hunit : IsUnit ((algebraMap ℝ (H01 Ω →L[ℝ] H01 Ω)) μ - Op.opK Ω) :=
        spectrum.mem_resolventSet_iff.mp hr
      set c : ℝ := (Op.gardingγ + lam) / Op.gardingγ with hcdef
      have hc0 : c ≠ 0 := div_ne_zero hcase hγ.ne'
      have hcμ : c * μ = 1 := by
        rw [hcdef, hμdef]
        field_simp
      have hfac : (1 : H01 Ω →L[ℝ] H01 Ω) - c • Op.opK Ω
          = (algebraMap ℝ (H01 Ω →L[ℝ] H01 Ω)) c
            * ((algebraMap ℝ (H01 Ω →L[ℝ] H01 Ω)) μ - Op.opK Ω) := by
        rw [mul_sub, ← map_mul, hcμ, map_one, ← Algebra.smul_def]
      have hcunit : IsUnit ((algebraMap ℝ (H01 Ω →L[ℝ] H01 Ω)) c) :=
        (isUnit_iff_ne_zero.mpr hc0).map (algebraMap ℝ (H01 Ω →L[ℝ] H01 Ω))
      have hKunit : IsUnit ((1 : H01 Ω →L[ℝ] H01 Ω) - c • Op.opK Ω) := by
        rw [hfac]
        exact hcunit.mul hunit
      have h1bij : Function.Bijective
          ((1 : H01 Ω →L[ℝ] H01 Ω) - c • Op.opK Ω) :=
        ContinuousLinearMap.isUnit_iff_bijective.mp hKunit
      have hEbij : Function.Bijective (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω) := by
        simpa using (Op.opE Ω).bijective
      rw [Op.opAlam_factor Ω lam]
      exact hEbij.comp h1bij

/-- A point of `Σ` defeats uniqueness already for `f = 0`: the eigenvector of `opK` at
`γ/(γ+λ)` is a nonzero weak solution of the homogeneous `λ`-problem. -/
lemma not_unique_of_mem_sigmaSet {lam : ℝ} (hlam : lam ∈ Op.sigmaSet Ω) :
    ¬ ∃! u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = lam * zerothForm Ω u v := by
  obtain ⟨hne, heig⟩ := hlam
  obtain ⟨x, hx_mem, hx_ne⟩ := heig.exists_hasEigenvector
  have hγ := Op.gardingγ_pos
  have hKx : Op.opK Ω x = (Op.gardingγ / (Op.gardingγ + lam)) • x := by
    simpa using Module.End.mem_eigenspace_iff.mp hx_mem
  -- `opAlam x = 0`
  have hAx : Op.opAlam Ω lam x = 0 := by
    rw [Op.opAlam_factor Ω lam, ContinuousLinearMap.comp_apply]
    have h0 : ((1 : H01 Ω →L[ℝ] H01 Ω)
        - ((Op.gardingγ + lam) / Op.gardingγ) • Op.opK Ω) x = 0 := by
      rw [_root_.sub_apply, one_apply_eq_self,
        _root_.smul_apply, hKx, smul_smul]
      rw [show (Op.gardingγ + lam) / Op.gardingγ * (Op.gardingγ / (Op.gardingγ + lam))
          = 1 by field_simp]
      rw [one_smul, sub_self]
    rw [h0, map_zero]
  -- `x` solves the homogeneous problem
  have hxsol : ∀ v : H01 Ω, Op.fullBilin Ω x v = lam * zerothForm Ω x v := by
    intro v
    have h1 := Op.inner_opAlam Ω lam x v
    rw [hAx, inner_zero_left] at h1
    linarith [h1]
  -- `0` solves it too
  have h0sol : ∀ v : H01 Ω, Op.fullBilin Ω (0 : H01 Ω) v
      = lam * zerothForm Ω (0 : H01 Ω) v := by
    intro v
    simp
  rintro ⟨u, -, huniq⟩
  exact hx_ne (by rw [huniq x hxsol, huniq 0 h0sol])

/-- Off `Σ`, the `λ`-shifted weak problem is uniquely solvable for every functional. -/
theorem solvable_of_notMem_sigmaSet (hK : IsCompactOperator (Op.opK Ω)) {lam : ℝ}
    (hlam : lam ∉ Op.sigmaSet Ω) (f : H01 Ω →L[ℝ] ℝ) :
    ∃! u : H01 Ω, ∀ v : H01 Ω,
      Op.fullBilin Ω u v = lam * zerothForm Ω u v + f v := by
  have hbij := Op.opAlam_bijective_of_notMem Ω hK hlam
  exact (existsUnique_congr (fun u =>
    (Op.opAlam_solves_iff Ω lam f u).symm)).mp
    (hbij.existsUnique ((InnerProductSpace.toDual ℝ (H01 Ω)).symm f))

/-- The membership characterisation of `Σ` (the `H⁻¹` form of Existence III(i)):
`λ ∉ Σ` exactly when `B[u,v] = λ⟨u₀,v₀⟩ + f(v)` is uniquely solvable for every `f`. -/
theorem notMem_sigmaSet_iff_solvable (hK : IsCompactOperator (Op.opK Ω)) (lam : ℝ) :
    lam ∉ Op.sigmaSet Ω
      ↔ ∀ f : H01 Ω →L[ℝ] ℝ, ∃! u : H01 Ω, ∀ v : H01 Ω,
          Op.fullBilin Ω u v = lam * zerothForm Ω u v + f v := by
  constructor
  · exact fun h f => Op.solvable_of_notMem_sigmaSet Ω hK h f
  · intro hall
    by_contra hmem
    apply Op.not_unique_of_mem_sigmaSet Ω hmem
    have h0 := hall 0
    refine (existsUnique_congr (fun u => forall_congr' (fun v => ?_))).mp h0
    simp

/-- Bounded-above slices of `Σ` are finite: a `λ ∈ Σ ∩ Iic C` has
`μ(λ) = γ/(γ+λ) ≥ γ/(γ+C) > 0` (positivity of the `opK` eigenvalues bounds `Σ`
inside `(-γ, ∞)`), and only finitely many such eigenvalues exist. -/
theorem sigmaSet_inter_Iic_finite (hK : IsCompactOperator (Op.opK Ω)) (C : ℝ) :
    (Op.sigmaSet Ω ∩ Set.Iic C).Finite := by
  have hγ := Op.gardingγ_pos
  -- `γ + λ > 0` on `Σ`
  have hposmem : ∀ lam ∈ Op.sigmaSet Ω, 0 < Op.gardingγ + lam := by
    rintro lam ⟨hne, heig⟩
    have hμpos : 0 < Op.gardingγ / (Op.gardingγ + lam) :=
      Op.opK_eigenvalue_pos Ω heig (div_ne_zero hγ.ne' hne)
    by_contra hneg
    push Not at hneg
    have h2 : Op.gardingγ / (Op.gardingγ + lam) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos hγ.le hneg
    linarith
  by_cases hC : Op.gardingγ + C ≤ 0
  · convert Set.finite_empty
    rw [Set.eq_empty_iff_forall_notMem]
    rintro lam ⟨hmem, hle⟩
    have h1 := hposmem lam hmem
    rw [Set.mem_Iic] at hle
    linarith
  · push Not at hC
    set δ : ℝ := Op.gardingγ / (Op.gardingγ + C) with hδdef
    have hδ : 0 < δ := div_pos hγ hC
    have himg : (fun lam => Op.gardingγ / (Op.gardingγ + lam))
          '' (Op.sigmaSet Ω ∩ Set.Iic C)
        ⊆ {μ : ℝ | Module.End.HasEigenvalue (Op.opK Ω).toLinearMap μ ∧ δ ≤ |μ|} := by
      rintro _ ⟨lam, ⟨hmem, hle⟩, rfl⟩
      obtain ⟨hne, heig⟩ := hmem
      have hpos := hposmem lam ⟨hne, heig⟩
      rw [Set.mem_Iic] at hle
      refine ⟨heig, ?_⟩
      have hμpos : 0 < Op.gardingγ / (Op.gardingγ + lam) :=
        Op.opK_eigenvalue_pos Ω heig (div_ne_zero hγ.ne' hne)
      rw [abs_of_pos hμpos, hδdef]
      gcongr
    have hfin : ((fun lam => Op.gardingγ / (Op.gardingγ + lam))
        '' (Op.sigmaSet Ω ∩ Set.Iic C)).Finite :=
      (finite_setOf_hasEigenvalue_abs_ge hK hδ).subset himg
    refine Set.Finite.of_finite_image hfin ?_
    rintro lam1 hlam1 lam2 hlam2 heq
    have hpos1 := hposmem lam1 hlam1.1
    have hpos2 := hposmem lam2 hlam2.1
    rw [div_eq_div_iff hpos1.ne' hpos2.ne'] at heq
    have h2 := mul_left_cancel₀ hγ.ne' heq
    linarith

/-- The exceptional set `Σ` is countable: finite on each bounded slice `Σ ∩ (-∞, n]`. -/
theorem sigmaSet_countable (hK : IsCompactOperator (Op.opK Ω)) :
    (Op.sigmaSet Ω).Countable := by
  have hsub : Op.sigmaSet Ω ⊆ ⋃ n : ℕ, (Op.sigmaSet Ω ∩ Set.Iic (n : ℝ)) := by
    intro lam hlam
    obtain ⟨n, hn⟩ := exists_nat_ge lam
    exact Set.mem_iUnion.mpr ⟨n, hlam, hn⟩
  exact Set.Countable.mono hsub
    (Set.countable_iUnion (fun n => (Op.sigmaSet_inter_Iic_finite Ω hK n).countable))

/-- The zero `L²` right-hand side contributes a vanishing integral. -/
private lemma integral_zero_rhs (v : H01 Ω) :
    (∫ x in Ω, ((0 : L2D Ω) x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) = 0 := by
  have h1 : (∫ x in Ω, ((0 : L2D Ω) x : ℝ) * ((v : H1amb Ω) 0 x : ℝ))
      = ∫ _x in Ω, (0 : ℝ) := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with a ha
    rw [ha]
    simp
  rw [h1, integral_zero]

/-- **Existence III.** There is a set `Σ ⊆ ℝ`, countable and with
finite intersection with every `(-∞, C]` (so an infinite `Σ` is a nondecreasing
sequence diverging to `+∞`), such that for every `λ ∉ Σ` and every `f ∈ L²(Ω)` the
weak problem `Lu = λu + f` (`B[u,v] = λ⟨u₀,v₀⟩ + ∫_Ω f v₀` for all `v`) has a
unique solution `u ∈ H₀¹(Ω)`, and for `λ ∈ Σ` uniqueness fails. -/
theorem existence_three (hK : IsCompactOperator (Op.opK Ω)) :
    ∃ S : Set ℝ, S.Countable ∧ (∀ C : ℝ, (S ∩ Set.Iic C).Finite) ∧
      ∀ lam : ℝ, lam ∉ S ↔ ∀ f : L2D Ω, ∃! u : H01 Ω, ∀ v : H01 Ω,
        Op.fullBilin Ω u v
          = lam * ⟪(u : H1amb Ω) 0, ((v : H1amb Ω) 0)⟫
            + ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ) := by
  refine ⟨Op.sigmaSet Ω, Op.sigmaSet_countable Ω hK,
    fun C => Op.sigmaSet_inter_Iic_finite Ω hK C, fun lam => ?_⟩
  constructor
  · intro hlam f
    have h1 := Op.solvable_of_notMem_sigmaSet Ω hK hlam (l2Functional Ω f)
    refine (existsUnique_congr (fun u => forall_congr' (fun v => ?_))).mp h1
    rw [l2Functional_eq_integral, zerothForm_apply]
  · intro hall
    by_contra hmem
    apply Op.not_unique_of_mem_sigmaSet Ω hmem
    have h0 := hall 0
    refine (existsUnique_congr (fun u => forall_congr' (fun v => ?_))).mp h0
    rw [integral_zero_rhs Ω v, add_zero, zerothForm_apply]

/-- **Boundedness of the resolvent.** For `λ ∉ Σ` there is a
constant `C > 0` such that every weak solution of `Lu = λu + f` with `f ∈ L²(Ω)`
satisfies `‖u‖_{L²} ≤ C ‖f‖_{L²}`. The constant is the operator norm of the
continuous inverse of the `λ`-shifted Riesz operator. -/
theorem resolvent_bound (hK : IsCompactOperator (Op.opK Ω)) {lam : ℝ}
    (hlam : lam ∉ Op.sigmaSet Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : L2D Ω, ∀ u : H01 Ω,
      (∀ v : H01 Ω, Op.fullBilin Ω u v
        = lam * ⟪(u : H1amb Ω) 0, ((v : H1amb Ω) 0)⟫
          + ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) →
      ‖(u : H1amb Ω) 0‖ ≤ C * ‖f‖ := by
  have hbij := Op.opAlam_bijective_of_notMem Ω hK hlam
  have hunit : IsUnit (Op.opAlam Ω lam) :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr hbij
  obtain ⟨w, hw⟩ := hunit
  set B : H01 Ω →L[ℝ] H01 Ω := ↑w⁻¹ with hBdef
  have hBA : ∀ y : H01 Ω, B (Op.opAlam Ω lam y) = y := by
    intro y
    have h1 : B * Op.opAlam Ω lam = 1 := by
      rw [hBdef, ← hw]
      exact w.inv_mul
    calc B (Op.opAlam Ω lam y) = (B * Op.opAlam Ω lam) y :=
        (mul_apply_eq_comp _ _ _).symm
      _ = (1 : H01 Ω →L[ℝ] H01 Ω) y := by rw [h1]
      _ = y := rfl
  refine ⟨‖B‖ + 1, by positivity, ?_⟩
  intro f u hu
  have hu' : ∀ v : H01 Ω, Op.fullBilin Ω u v
      = lam * zerothForm Ω u v + l2Functional Ω f v := by
    intro v
    rw [zerothForm_apply, l2Functional_eq_integral]
    exact hu v
  have hAu : Op.opAlam Ω lam u
      = (InnerProductSpace.toDual ℝ (H01 Ω)).symm (l2Functional Ω f) :=
    (Op.opAlam_solves_iff Ω lam (l2Functional Ω f) u).mp hu'
  have hub : ‖u‖ ≤ ‖B‖ * ‖f‖ := by
    calc ‖u‖ = ‖B (Op.opAlam Ω lam u)‖ := by rw [hBA u]
      _ ≤ ‖B‖ * ‖Op.opAlam Ω lam u‖ := B.le_opNorm _
      _ = ‖B‖ * ‖(InnerProductSpace.toDual ℝ (H01 Ω)).symm (l2Functional Ω f)‖ := by
          rw [hAu]
      _ = ‖B‖ * ‖l2Functional Ω f‖ := by
          rw [LinearIsometryEquiv.norm_map]
      _ ≤ ‖B‖ * ‖f‖ :=
          mul_le_mul_of_nonneg_left (norm_l2Functional_le Ω f) (norm_nonneg B)
  calc ‖(u : H1amb Ω) 0‖ ≤ ‖u‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖B‖ * ‖f‖ := hub
    _ ≤ (‖B‖ + 1) * ‖f‖ :=
        mul_le_mul_of_nonneg_right (by linarith [norm_nonneg B]) (norm_nonneg f)

end FullEllipticOp

end EllipticPdes.Sobolev
