/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Manifolds.SmoothDomain

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Besov spaces of smooth domains by charts

For a smooth bounded domain `Ω ⊆ ℝ^n` the Besov space of the compact manifold `closure Ω` with
the Lebesgue measure, defined by charts, is the space of functions on `Ω` with finite intrinsic
Besov quasi-norm (`Rd.SmoothDomain.memBesov_iff_modNormOn_lt_top`):

`f ∈ B^s_{p,q}(closure Ω)  ↔  ‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`

for `0 < s < r`, with `f` extended by `0` to `ℝ^n` (`Rd.SmoothDomain.extLp`).

The proof uses a **global atlas** (`Rd.SmoothDomain.GlobalAtlas`): finitely many straighteners
and a partition of unity and cut-offs that are smooth functions on `ℝ^n`
(`Rd.SmoothDomain.GlobalAtlas.nonempty`). Its pieces are the global functions
`(ψ_i f) ∘ τ_i` on the half-space (`Rd.SmoothDomain.GlobalAtlas.indicator_piece`). If `f` agrees
on `Ω` with some `F ∈ B^s_{p,q}(ℝ^n)` (Rychkov's extension, for finite intrinsic quasi-norm), the
pieces are the changes of variables `(ψ_i F) ∘ τ_i` of `F` on the half-space, which are bounded.
Conversely, the pieces extend from the half-space to `G_i ∈ B^s_{p,q}(ℝ^n)`, and
`F = ∑_i θ_i (G_i ∘ σ_i)` agrees with `f` on `Ω`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Manifold ContDiff

open ENNReal (lqNorm dyadicWeight)

namespace Rd

namespace SmoothDomain

variable {n : ℕ} [NeZero n] (Ω : SmoothDomain n)

/-! ### The global atlas -/

/-- A **global atlas** of the closure of a smooth domain: finitely many straighteners whose sets
cover the closure, a smooth partition of unity on `ℝ^n` subordinate to them on the closure, and
smooth cut-offs `θ_i = 1` on `tsupport ψ_i`, all with supports inside the sets. -/
structure GlobalAtlas where
  /-- The number of charts. -/
  N : ℕ
  /-- The straighteners. -/
  S : Fin N → Ω.Straightener
  /-- The partition of unity. -/
  psi : Fin N → EuclideanSpace ℝ (Fin n) → ℝ
  contDiff_psi : ∀ i, ContDiff ℝ ∞ (psi i)
  nonneg_psi : ∀ i x, 0 ≤ psi i x
  tsupport_psi_subset : ∀ i, tsupport (psi i) ⊆ (S i).B
  sum_psi : ∀ x ∈ closure Ω.carrier, ∑ i, psi i x = 1
  /-- The cut-offs. -/
  theta : Fin N → EuclideanSpace ℝ (Fin n) → ℝ
  contDiff_theta : ∀ i, ContDiff ℝ ∞ (theta i)
  theta_eq_one : ∀ i, ∀ x ∈ tsupport (psi i), theta i x = 1
  tsupport_theta_subset : ∀ i, tsupport (theta i) ⊆ (S i).B

/-- **Every smooth domain has a global atlas**: finitely many sets of straighteners cover the
compact closure, Mathlib's smooth partitions of unity on `ℝ^n` are subordinate to them, and smooth
cut-offs exist for every compact set inside an open set
(`Manifold.exists_contMDiff_eq_one_tsupport_subset`). -/
theorem GlobalAtlas.nonempty : Nonempty Ω.GlobalAtlas := by
  obtain ⟨t, ht⟩ := Ω.isCompact_closure.elim_finite_subcover
    (fun x : closure Ω.carrier => (Ω.straightenerAt x).B) (fun x => (Ω.straightenerAt x).isOpen_B)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, Ω.mem_straightenerAt ⟨x, hx⟩⟩)
  set pt : Fin t.card → closure Ω.carrier := fun i => (t.equivFin.symm i : closure Ω.carrier)
  have hcover : closure Ω.carrier ⊆ ⋃ i, (Ω.straightenerAt (pt i)).B := fun x hx => by
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht hx)
    refine mem_iUnion.2 ⟨t.equivFin ⟨y, hy⟩, ?_⟩
    simpa [pt] using hxy
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    isClosed_closure (fun i => (Ω.straightenerAt (pt i)).B)
    (fun i => (Ω.straightenerAt (pt i)).isOpen_B) hcover
  have hθ : ∀ i, ∃ θ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ θ ∧
      (∀ x ∈ tsupport (f i), θ x = 1) ∧ tsupport θ ⊆ (Ω.straightenerAt (pt i)).B := fun i => by
    obtain ⟨θ, hθs, hθ1, hθsub⟩ := Manifold.exists_contMDiff_eq_one_tsupport_subset
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (Metric.isCompact_of_isClosed_isBounded
        (isClosed_tsupport _) ((Ω.straightenerAt (pt i)).isBounded_B.subset (hf i)))
      (Ω.straightenerAt (pt i)).isOpen_B (hf i)
    exact ⟨θ, contMDiff_iff_contDiff.1 hθs, hθ1, hθsub⟩
  choose θ hθs hθ1 hθsub using hθ
  exact ⟨{ N := t.card
           S := fun i => Ω.straightenerAt (pt i)
           psi := fun i => f i
           contDiff_psi := fun i => contMDiff_iff_contDiff.1 (f i).contMDiff
           nonneg_psi := fun i x => f.nonneg i x
           tsupport_psi_subset := hf
           sum_psi := fun x hx => by
             have h := f.sum_eq_one hx
             rwa [finsum_eq_sum_of_fintype] at h
           theta := θ
           contDiff_theta := hθs
           theta_eq_one := hθ1
           tsupport_theta_subset := hθsub }⟩

variable {Ω}

/-- **The Besov atlas of a global atlas**: the charts of the straighteners and the restrictions of
the partition of unity and of the cut-offs to the closure. -/
noncomputable def GlobalAtlas.toBesovAtlas (G : Ω.GlobalAtlas) :
    Manifold.BesovAtlas (𝓡∂ n) (closure Ω.carrier) where
  n := G.N
  chart i := (G.S i).chart
  chart_mem i := ⟨G.S i, rfl⟩
  psi i x := G.psi i x
  contMDiff_psi i :=
    (contMDiff_iff_contDiff.2 (G.contDiff_psi i)).comp Ω.contMDiff_subtype_val
  nonneg_psi i x := G.nonneg_psi i x
  tsupport_psi_subset i :=
    (tsupport_comp_subset_preimage (G.psi i) continuous_subtype_val).trans
      (preimage_mono (G.tsupport_psi_subset i))
  sum_psi x := G.sum_psi x x.2
  theta i x := G.theta i x
  contMDiff_theta i :=
    (contMDiff_iff_contDiff.2 (G.contDiff_theta i)).comp Ω.contMDiff_subtype_val
  theta_eq_one i x hx :=
    G.theta_eq_one i x (tsupport_comp_subset_preimage (G.psi i) continuous_subtype_val hx)
  tsupport_theta_subset i :=
    (tsupport_comp_subset_preimage (G.theta i) continuous_subtype_val).trans
      (preimage_mono (G.tsupport_theta_subset i))

/-! ### Extension by zero -/

variable (Ω)

/-- The **extension by `0`** of a function on the closure to `ℝ^n`. -/
noncomputable def extend (g : closure Ω.carrier → ℂ) : EuclideanSpace ℝ (Fin n) → ℂ :=
  Function.extend Subtype.val g 0

variable {Ω}

/-- The extension agrees with the function on the closure. -/
theorem extend_coe (g : closure Ω.carrier → ℂ) (x : closure Ω.carrier) :
    Ω.extend g x = g x :=
  Subtype.val_injective.extend_apply g 0 x

/-- The extension vanishes outside the closure. -/
theorem extend_eq_zero (g : closure Ω.carrier → ℂ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∉ closure Ω.carrier) : Ω.extend g x = 0 :=
  Function.extend_val_apply' hx

/-- The extension of a strongly measurable function is strongly measurable. -/
theorem stronglyMeasurable_extend {g : closure Ω.carrier → ℂ} (hg : StronglyMeasurable g) :
    StronglyMeasurable (Ω.extend g) :=
  (MeasurableEmbedding.subtype_coe isClosed_closure.measurableSet).stronglyMeasurable_extend hg
    stronglyMeasurable_const

/-- **The extension preserves `L_p` norms**: `‖ext g‖_{L_p(ℝ^n)} = ‖g‖_{L_p(closure Ω)}`. -/
theorem eLpNorm_extend {g : closure Ω.carrier → ℂ} (hg : StronglyMeasurable g) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ⊤) : eLpNorm (Ω.extend g) p volume = eLpNorm g p Ω.volumeOn := by
  have he : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hcl : MeasurableSet (closure Ω.carrier) := isClosed_closure.measurableSet
  refine ENNReal.rpow_left_injective he.ne' ?_
  simp only
  rw [eLpNorm_rpow_eq (Ω.stronglyMeasurable_extend hg).aestronglyMeasurable hp0 hp,
    eLpNorm_rpow_eq hg.aestronglyMeasurable hp0 hp]
  have hsupp : Function.support (fun x => ‖Ω.extend g x‖ₑ ^ p.toReal) ⊆ closure Ω.carrier :=
    fun x hx => by
      by_contra h
      exact hx (by simp only [extend_eq_zero g h, eNorm_zero, ENNReal.zero_rpow_of_pos he])
  rw [← setLIntegral_eq_of_support_subset hsupp, ← lintegral_subtype_comap hcl]
  simp only [extend_coe]
  rfl

/-! ### The pieces of the global atlas -/

omit [NeZero n] in
/-- `{y : y_0 = 0}` is a null set: it is the hyperplane `e₀^⊥`
(`Rd.volume_orthogonal_singleton_eq_zero`). -/
theorem volume_coord_zero_eq_zero [NeZero n] :
    volume {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} = 0 := by
  have h : {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} =
      ((ℝ ∙ (e0 : EuclideanSpace ℝ (Fin n)))ᗮ : Set (EuclideanSpace ℝ (Fin n))) := by
    ext y
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm,
      ← coord_zero_eq_inner]
    rfl
  rw [h]
  exact volume_orthogonal_singleton_eq_zero (norm_ne_zero_iff.1 (by simp [norm_e0]))

namespace Straightener

variable (S : Ω.Straightener)

/-- The image `σ(closure Ω ∩ B)` is `{y : 0 ≤ y_0, τ(y) ∈ B}`. -/
theorem mem_image_iff {y : EuclideanSpace ℝ (Fin n)} :
    y ∈ S.sigma '' (closure Ω.carrier ∩ S.B) ↔ 0 ≤ y 0 ∧ S.tau y ∈ S.B := by
  constructor
  · rintro ⟨x, ⟨hxcl, hxB⟩, rfl⟩
    exact ⟨(S.mem_closure_iff x hxB).1 hxcl, by rwa [S.tau_sigma]⟩
  · rintro ⟨hy, hyB⟩
    exact ⟨S.tau y, ⟨S.tau_mem_closure hy hyB, hyB⟩, S.sigma_tau y⟩

/-- The homeomorphism `σ` of `ℝ^n`. -/
noncomputable def homeomorph : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  Homeomorph.mk ⟨S.sigma, S.tau, S.tau_sigma, S.sigma_tau⟩ S.contDiff_sigma.continuous
    S.contDiff_tau.continuous

/-- `τ` preserves the Lebesgue measure. -/
theorem measurePreserving_tau : MeasurePreserving S.tau volume volume :=
  MeasurePreserving.symm S.homeomorph.toMeasurableEquiv S.measurePreserving_sigma

end Straightener

namespace GlobalAtlas

variable (G : Ω.GlobalAtlas)

/-- The partition of unity has compact supports. -/
theorem hasCompactSupport_psi (i : Fin G.N) : HasCompactSupport (G.psi i) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _)
    ((G.S i).isBounded_B.subset (G.tsupport_psi_subset i))

/-- The cut-offs have compact supports. -/
theorem hasCompactSupport_theta (i : Fin G.N) : HasCompactSupport (G.theta i) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _)
    ((G.S i).isBounded_B.subset (G.tsupport_theta_subset i))

/-- `ψ_i = 0` outside `B_i`. -/
theorem psi_eq_zero (i : Fin G.N) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ (G.S i).B) :
    G.psi i x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (G.tsupport_psi_subset i h)

/-- `θ_i = 0` outside `B_i`. -/
theorem theta_eq_zero (i : Fin G.N) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ (G.S i).B) :
    G.theta i x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (G.tsupport_theta_subset i h)

/-- `θ_i ψ_i = ψ_i`. -/
theorem theta_mul_psi (i : Fin G.N) (x : EuclideanSpace ℝ (Fin n)) :
    G.theta i x * G.psi i x = G.psi i x := by
  by_cases hx : x ∈ tsupport (G.psi i)
  · rw [G.theta_eq_one i x hx, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-- **The pieces of the global atlas**: `piece_i g = 1_{σ_i(closure Ω ∩ B_i)} (ψ_i ext g) ∘ τ_i`. -/
theorem piece_apply (i : Fin G.N) (g : closure Ω.carrier → ℂ) (y : EuclideanSpace ℝ (Fin n)) :
    G.toBesovAtlas.piece i g y = ((G.S i).sigma '' (closure Ω.carrier ∩ (G.S i).B)).indicator
      (fun y => (G.psi i ((G.S i).tau y) : ℂ) * Ω.extend g ((G.S i).tau y)) y := by
  have ht : (G.toBesovAtlas.ext i).target = (G.S i).sigma '' (closure Ω.carrier ∩ (G.S i).B) :=
    (G.S i).extend_target
  unfold Manifold.BesovAtlas.piece
  rw [ht]
  by_cases hy : y ∈ (G.S i).sigma '' (closure Ω.carrier ∩ (G.S i).B)
  · rw [indicator_of_mem hy, indicator_of_mem hy]
    obtain ⟨hy0, hyB⟩ := (G.S i).mem_image_iff.1 hy
    have hyI : y ∈ range (𝓡∂ n) := by
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact hy0
    have hyy : (𝓡∂ n) ((𝓡∂ n).symm y) = y := (𝓡∂ n).right_inv hyI
    have hcoe : (((G.toBesovAtlas.ext i).symm y : closure Ω.carrier) :
        EuclideanSpace ℝ (Fin n)) = (G.S i).tau y := by
      rw [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply]
      have h := (G.S i).chart_symm_coe (y := (𝓡∂ n).symm y) (by rw [hyy]; exact hyB)
      rw [hyy] at h
      exact h
    rw [← hcoe, extend_coe]
    rfl
  · rw [indicator_of_notMem hy, indicator_of_notMem hy]

/-- **The pieces on the half-space**: `1_{y_0 ≥ 0} piece_i g = 1_{y_0 ≥ 0} (ψ_i ext g) ∘ τ_i`. -/
theorem indicator_piece (i : Fin G.N) (g : closure Ω.carrier → ℂ) :
    (range (𝓡∂ n)).indicator (G.toBesovAtlas.piece i g) = (range (𝓡∂ n)).indicator
      (fun y => (G.psi i ((G.S i).tau y) : ℂ) * Ω.extend g ((G.S i).tau y)) := by
  funext y
  by_cases hyI : y ∈ range (𝓡∂ n)
  · rw [indicator_of_mem hyI, indicator_of_mem hyI, G.piece_apply]
    have hy0 : 0 ≤ y 0 := by rwa [range_modelWithCornersEuclideanHalfSpace] at hyI
    by_cases hyB : (G.S i).tau y ∈ (G.S i).B
    · rw [indicator_of_mem ((G.S i).mem_image_iff.2 ⟨hy0, hyB⟩)]
    · rw [indicator_of_notMem fun h => hyB ((G.S i).mem_image_iff.1 h).2,
        G.psi_eq_zero i hyB, Complex.ofReal_zero, zero_mul]
  · rw [indicator_of_notMem hyI, indicator_of_notMem hyI]

end GlobalAtlas

/-! ### The `L_p` bridge -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)

include hp in
/-- The extension of `f ∈ L_p(closure Ω)` is in `L_p(ℝ^n)`. -/
theorem memLp_extend (f : Lp ℂ p Ω.volumeOn) : MemLp (Ω.extend f) p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  rw [memLp_iff, eLpNorm_extend (Lp.stronglyMeasurable f) hp0 hp]
  exact Lp.eLpNorm_lt_top f

variable (Ω) in
/-- The **extension by `0`** of `f ∈ L_p(closure Ω)` as an element of `L_p(ℝ^n)`. -/
noncomputable def extLp (f : Lp ℂ p Ω.volumeOn) :
    Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (memLp_extend hp f).toLp _

/-- The extension in `L_p` is the extension by `0`, almost everywhere. -/
theorem extLp_ae (f : Lp ℂ p Ω.volumeOn) : Ω.extLp hp f =ᵐ[volume] Ω.extend f :=
  MemLp.coeFn_toLp _

/-! ### The changes of variables between the domain and the charts -/

namespace GlobalAtlas

variable (G : Ω.GlobalAtlas)

/-- The change of variables `F ↦ (ψ_i F) ∘ τ_i` from `ℝ^n` to the `i`-th chart. -/
noncomputable def toChart (i : Fin G.N) :
    CutoffDiffeo (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
  CutoffDiffeo.global (G.S i).tau (G.S i).sigma (G.S i).contDiff_tau (G.S i).contDiff_sigma
    (G.S i).sigma_tau (G.S i).tau_sigma (fun x => (G.psi i x : ℂ))
    (Complex.ofRealCLM.contDiff.comp (G.contDiff_psi i))
    ((G.hasCompactSupport_psi i).comp_left Complex.ofReal_zero)

/-- `T_i F = (ψ_i F) ∘ τ_i`. -/
theorem toChart_apply (i : Fin G.N) (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (y : EuclideanSpace ℝ (Fin n)) :
    (G.toChart i).apply F y = (G.psi i ((G.S i).tau y) : ℂ) * F ((G.S i).tau y) :=
  CutoffDiffeo.global_apply _ _ _ _ _ _ _ _ _ F y

/-- The change of variables `G ↦ θ_i (G ∘ σ_i)` from the `i`-th chart to `ℝ^n`. -/
noncomputable def fromChart (i : Fin G.N) :
    CutoffDiffeo (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
  CutoffDiffeo.global (G.S i).sigma (G.S i).tau (G.S i).contDiff_sigma (G.S i).contDiff_tau
    (G.S i).tau_sigma (G.S i).sigma_tau (fun y => (G.theta i ((G.S i).tau y) : ℂ))
    (Complex.ofRealCLM.contDiff.comp ((G.contDiff_theta i).comp (G.S i).contDiff_tau))
    (((G.hasCompactSupport_theta i).comp_left Complex.ofReal_zero).comp_homeomorph
      (G.S i).homeomorph.symm)

/-- `T'_i G = θ_i (G ∘ σ_i)`. -/
theorem fromChart_apply (i : Fin G.N) (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (G.fromChart i).apply F x = (G.theta i x : ℂ) * F ((G.S i).sigma x) := by
  rw [CutoffDiffeo.apply, Set.indicator_of_mem]
  · change ((G.theta i ((G.S i).tau ((G.S i).sigma x)) : ℝ) : ℂ) * F ((G.S i).sigma x) = _
    rw [(G.S i).tau_sigma]
  · exact ⟨Set.mem_univ x, Set.mem_univ x⟩

end GlobalAtlas

/-! ### The Besov space of the closure -/

variable [Rd.BesovDomain (range (𝓡∂ n))]

omit [NeZero n] [Rd.BesovDomain (range (𝓡∂ n))] in
/-- The whole space has nonempty interior. -/
theorem interior_univ_nonempty :
    (interior (Set.univ : Set (EuclideanSpace ℝ (Fin n)))).Nonempty := by
  rw [interior_univ]
  exact univ_nonempty

/-- **From the domain to the charts**: if `f` has a finite intrinsic Besov quasi-norm on `Ω`, its
pieces have finite intrinsic Besov quasi-norms on the half-space: `f` agrees on `Ω` with some
`F ∈ B^s_{p,q}(ℝ^n)`, and on the half-space the piece `(ψ_i f) ∘ τ_i` agrees with `(ψ_i F) ∘ τ_i`,
since `τ_i` maps the open half-space into `Ω` near `tsupport ψ_i` and preserves null sets. -/
theorem GlobalAtlas.modNormOn_pieceLp_lt_top (G : Ω.GlobalAtlas) {r : ℕ} {s : ℝ} (hs : 0 < s)
    (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p Ω.volumeOn)
    (hf : modNormOn Ω.measurableSet r s q (Ω.extLp hp f) < ⊤) (i : Fin G.N) :
    modNormOn (BesovDomain.measurableSet (range (𝓡∂ n))) r s q
      (G.toBesovAtlas.pieceLp Ω.volumeOn hp i f) < ⊤ := by
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (Nat.cast_pos.1 (hs.trans hsr)).ne'
  set hΩh := BesovDomain.measurableSet (range (𝓡∂ n))
  obtain ⟨F, hFf, hF⟩ :=
    (Ω.exists_besov_extension_iff_modulusOn hp hs hsr hq (Ω.extLp hp f)).2 hf
  set T := G.toChart i
  obtain ⟨C, hC, hT⟩ := T.modNormOn_applyLp_le convex_univ interior_univ_nonempty
    MeasurableSet.univ hp hr hs hsr hq
  -- `f = F` on `Ω`
  have hΩf : ∀ᵐ x ∂volume, x ∈ Ω.carrier → Ω.extend f x = F x := by
    filter_upwards [(ae_restrict_iff' Ω.measurableSet).1
      ((indicatorLp_eq_iff_ae_eq_restrict Ω.measurableSet).1 hFf), Ω.extLp_ae hp f]
      with x h1 h3 hx
    rw [h1 hx, h3]
  -- the piece agrees with `(ψ_i F) ∘ τ_i` on the half-space
  have hgood : ∀ᵐ y ∂volume, y ∈ range (𝓡∂ n) →
      (G.psi i ((G.S i).tau y) : ℂ) * Ω.extend f ((G.S i).tau y) =
        (G.psi i ((G.S i).tau y) : ℂ) * F ((G.S i).tau y) := by
    have h0 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        y ∉ {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} :=
      measure_eq_zero_iff_ae_notMem.1 volume_coord_zero_eq_zero
    filter_upwards [(G.S i).measurePreserving_tau.quasiMeasurePreserving.ae hΩf, h0]
      with y h1 h2 hy
    by_cases hB : (G.S i).tau y ∈ (G.S i).B
    · have hy0 : 0 < y 0 := lt_of_le_of_ne
        (by rwa [range_modelWithCornersEuclideanHalfSpace] at hy) (fun h => h2 h.symm)
      have hΩ : (G.S i).tau y ∈ Ω.carrier :=
        ((G.S i).mem_iff _ hB).2 (by rwa [(G.S i).sigma_tau])
      rw [h1 hΩ]
    · rw [G.psi_eq_zero i hB, Complex.ofReal_zero, zero_mul, zero_mul]
  have hind : indicatorLp hΩh (G.toBesovAtlas.pieceLp Ω.volumeOn hp i f) =
      indicatorLp hΩh (T.applyLp convex_univ interior_univ_nonempty MeasurableSet.univ hp F) := by
    refine Lp.ext ?_
    filter_upwards [indicatorLp_apply_ae hΩh (G.toBesovAtlas.pieceLp Ω.volumeOn hp i f),
      indicatorLp_apply_ae hΩh (T.applyLp convex_univ interior_univ_nonempty MeasurableSet.univ
        hp F), G.toBesovAtlas.pieceLp_ae Ω.volumeOn hp i f,
      T.applyLp_ae convex_univ interior_univ_nonempty MeasurableSet.univ hp F, hgood]
      with y h1 h2 h3 h4 h5
    rw [h1, h2]
    by_cases hy : y ∈ range (𝓡∂ n)
    · have hp' := congrFun (G.indicator_piece i f) y
      rw [indicator_of_mem hy, indicator_of_mem hy] at hp' ⊢
      rw [h3, h4, G.toChart_apply, hp', h5 hy]
    · rw [indicator_of_notMem hy, indicator_of_notMem hy]
  rw [modNormOn_congr hΩh hind]
  calc modNormOn hΩh r s q (T.applyLp convex_univ interior_univ_nonempty MeasurableSet.univ hp F)
      ≤ ‖T.applyLp convex_univ interior_univ_nonempty MeasurableSet.univ hp F‖ₑ + lqNorm q
          (fun k => dyadicWeight s k * lpModulus p r
            (T.applyLp convex_univ interior_univ_nonempty MeasurableSet.univ hp F) k) :=
        modNormOn_le_modNorm_of_indicatorLp hΩh r s q rfl
    _ = modNormOn MeasurableSet.univ r s q
          (T.applyLp convex_univ interior_univ_nonempty MeasurableSet.univ hp F) :=
        (modNormOn_univ r s q _).symm
    _ ≤ C * (‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k)) := hT F
    _ < ⊤ := ENNReal.mul_lt_top hC.lt_top hF

/-- **From the charts to the domain**: if the pieces of `f` have finite intrinsic Besov
quasi-norms on the half-space, they extend to `G_i ∈ B^s_{p,q}(ℝ^n)`, and
`F = ∑_i θ_i (G_i ∘ σ_i) ∈ B^s_{p,q}(ℝ^n)` agrees with `f` on `Ω`, since
`θ_i ψ_i = ψ_i` and `∑_i ψ_i = 1` on the closure. -/
theorem GlobalAtlas.modNormOn_extLp_lt_top (G : Ω.GlobalAtlas) {r : ℕ} {s : ℝ} (hs : 0 < s)
    (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p Ω.volumeOn)
    (hf : ∀ i, modNormOn (BesovDomain.measurableSet (range (𝓡∂ n))) r s q
      (G.toBesovAtlas.pieceLp Ω.volumeOn hp i f) < ⊤) :
    modNormOn Ω.measurableSet r s q (Ω.extLp hp f) < ⊤ := by
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (Nat.cast_pos.1 (hs.trans hsr)).ne'
  set hΩh := BesovDomain.measurableSet (range (𝓡∂ n))
  obtain ⟨Cext, hCext, hext⟩ :=
    BesovDomain.exists_extension (Ω := range (𝓡∂ n)) p hp r s hs hsr q hq
  choose Gi hGif hGile using fun i => hext _ (hf i)
  set T := fun i => G.fromChart i
  choose C hC hT using fun i => (T i).modNormOn_applyLp_le convex_univ interior_univ_nonempty
    MeasurableSet.univ hp hr hs hsr hq
  set F := ∑ i, (T i).applyLp convex_univ interior_univ_nonempty MeasurableSet.univ hp (Gi i)
  -- `F` has a finite quasi-norm on `ℝ^n`
  have hF : modNormOn MeasurableSet.univ r s q F < ⊤ := by
    refine (modNormOn_finsetSum_le MeasurableSet.univ r s hq _ _).trans_lt
      (ENNReal.sum_lt_top.2 fun i _ => ?_)
    have hGi : ‖Gi i‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r (Gi i) k) < ⊤ :=
      (hGile i).trans_lt (ENNReal.mul_lt_top hCext.lt_top (hf i))
    exact (hT i _).trans_lt (ENNReal.mul_lt_top (hC i).lt_top hGi)
  -- `θ_i (G_i ∘ σ_i) = ψ_i f` on `Ω`
  have hpiece : ∀ i, ∀ᵐ x ∂volume, x ∈ Ω.carrier →
      (G.theta i x : ℂ) * Gi i ((G.S i).sigma x) = (G.psi i x : ℂ) * Ω.extend f x := fun i => by
    have h1 : ∀ᵐ y ∂volume, y ∈ range (𝓡∂ n) → Gi i y = G.toBesovAtlas.piece i f y := by
      filter_upwards [(ae_restrict_iff' hΩh).1
        ((indicatorLp_eq_iff_ae_eq_restrict hΩh).1 (hGif i)),
        G.toBesovAtlas.pieceLp_ae Ω.volumeOn hp i f] with y a1 a3 hy
      rw [a1 hy, a3]
    filter_upwards [(G.S i).measurePreserving_sigma.quasiMeasurePreserving.ae h1] with x hx hxΩ
    by_cases hB : x ∈ (G.S i).B
    · have hσ0 : 0 < (G.S i).sigma x 0 := ((G.S i).mem_iff x hB).1 hxΩ
      have hσI : (G.S i).sigma x ∈ range (𝓡∂ n) := by
        rw [range_modelWithCornersEuclideanHalfSpace]
        exact hσ0.le
      rw [hx hσI, G.piece_apply, indicator_of_mem ((G.S i).mem_image_iff.2
        ⟨hσ0.le, by rwa [(G.S i).tau_sigma]⟩), (G.S i).tau_sigma]
      have h := congrArg (fun t : ℝ => (t : ℂ)) (G.theta_mul_psi i x)
      push_cast at h
      linear_combination Ω.extend f x * h
    · rw [G.theta_eq_zero i hB, G.psi_eq_zero i hB, Complex.ofReal_zero, zero_mul, zero_mul]
  -- `F = f` on `Ω`
  have hFΩ : indicatorLp Ω.measurableSet F = indicatorLp Ω.measurableSet (Ω.extLp hp f) := by
    refine Lp.ext ?_
    filter_upwards [indicatorLp_apply_ae Ω.measurableSet F,
      indicatorLp_apply_ae Ω.measurableSet (Ω.extLp hp f), Ω.extLp_ae hp f,
      Lp.coeFn_fun_finsetSum Finset.univ (fun i => (T i).applyLp convex_univ
        interior_univ_nonempty MeasurableSet.univ hp (Gi i)),
      ae_all_iff.2 fun i => (T i).applyLp_ae convex_univ interior_univ_nonempty
        MeasurableSet.univ hp (Gi i), ae_all_iff.2 hpiece] with x h1 h2 h3 h4 h5 h6
    rw [h1, h2]
    by_cases hx : x ∈ Ω.carrier
    · rw [indicator_of_mem hx, indicator_of_mem hx, h3, h4]
      simp only [h5, T, G.fromChart_apply]
      rw [Finset.sum_congr rfl fun i _ => h6 i hx, ← Finset.sum_mul, ← Complex.ofReal_sum,
        G.sum_psi x (subset_closure hx), Complex.ofReal_one, one_mul]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  rw [← modNormOn_congr Ω.measurableSet hFΩ]
  calc modNormOn Ω.measurableSet r s q F
      ≤ ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) :=
        modNormOn_le_modNorm_of_indicatorLp Ω.measurableSet r s q rfl
    _ = modNormOn MeasurableSet.univ r s q F := (modNormOn_univ r s q F).symm
    _ < ⊤ := hF

/-- **The Besov space of a smooth domain by charts is the intrinsic Besov space**: for a smooth
bounded domain `Ω ⊆ ℝ^n`, `1 ≤ p < ∞`, `0 < s < r` and `1 ≤ q ≤ ∞`, `f ∈ L_p(closure Ω)` lies in
the Besov space `B^s_{p,q}` of the compact manifold `closure Ω` with the Lebesgue measure iff
`‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`. -/
theorem memBesov_iff_modNormOn_lt_top {s : ℝ} (hs : 0 < s) {r : ℕ} (hsr : s < r) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p Ω.volumeOn) :
    Manifold.MemBesov (𝓡∂ n) Ω.volumeOn hp s q f ↔
      modNormOn Ω.measurableSet r s q (Ω.extLp hp f) < ⊤ := by
  obtain ⟨G⟩ := GlobalAtlas.nonempty Ω
  rw [Manifold.memBesov_iff (I := 𝓡∂ n) (μ := Ω.volumeOn) hp G.toBesovAtlas hs hq f,
    G.toBesovAtlas.memBesov_iff_besovNorm_lt_top hp hs hsr hq f,
    Manifold.BesovAtlas.besovNorm, ENNReal.sum_lt_top]
  exact ⟨fun h => G.modNormOn_extLp_lt_top hp hs hsr hq f fun i => h i (Finset.mem_univ i),
    fun h i _ => G.modNormOn_pieceLp_lt_top hp hs hsr hq f h i⟩

end SmoothDomain

end Rd
