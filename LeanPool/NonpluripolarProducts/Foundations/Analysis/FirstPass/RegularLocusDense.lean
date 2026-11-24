/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalHolomorphicInverse
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicVanishingDerivative
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.RegularPatchNeighborhood

/-!
# The regular locus of an analytic subset is dense

Every point of a complex analytic subset `A` of a complex manifold is a limit of points at
which `A` is regular of some dimension (`exists_regularAtDim_mem_nhds`,
`subset_closure_iUnion_regularLocus`).  No local parametrization theorem is used; the
argument is the classical rank maximization.

In a chart, `A` is the zero set `S` of finitely many holomorphic `f_i` on an open `W`.
Among the points `q` of `S` in a given open set pick one maximizing the number `R` of
holomorphic functions vanishing on `S` near `q` with linearly independent differentials at
`q`.  Completing `R` such functions `g` by linear forms `ℓ` gives holomorphic coordinates
`Φ = (ℓ, g)` near `q` in which `S ⊆ ℂ^j × {0}`, `j = n - R`.  If all
`h_i(w) = f_i(Φ⁻¹(w, 0))` vanish near `0`, then `S = Φ⁻¹(ℂ^j × {0})` near `q`, a flattening.
Otherwise some `h_i` does not vanish identically near `0`, and
`exists_fderiv_ne_zero_of_not_eventuallyEq_zero` yields `G` vanishing on
`{w | Φ⁻¹(w, 0) ∈ S}` with `dG(w*) ≠ 0` at a point of that set; then `G ∘ pr_j ∘ Φ` and the
`g`'s are `R + 1` functions vanishing on `S` near `Φ⁻¹(w*, 0)` with independent
differentials, contradicting maximality.
-/

@[expose] public section

open Set Filter Module
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass.RegularLocusDense

noncomputable section

variable {n : ℕ}

/-! ### Linear coordinates -/

/-- The projection `ℂ^n → ℂ^j` onto the first `j` coordinates. -/
def coordinateProjection (n j : ℕ) : ComplexModel n →L[ℂ] ComplexModel j :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun a : Fin j => if h : a.1 < n then z ⟨a.1, h⟩ else 0)
      map_add' := by
        intro z z'
        ext a
        by_cases h : a.1 < n <;> simp [h]
      map_smul' := by
        intro c z
        ext a
        by_cases h : a.1 < n <;> simp [h] }

/-- The inclusion `ℂ^j → ℂ^n`, `w ↦ (w, 0)`. -/
def coordinateInclusion (n j : ℕ) : ComplexModel j →L[ℂ] ComplexModel n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 (fun i : Fin n => if h : i.1 < j then w ⟨i.1, h⟩ else 0)
      map_add' := by
        intro w w'
        ext i
        by_cases h : i.1 < j <;> simp [h]
      map_smul' := by
        intro c w
        ext i
        by_cases h : i.1 < j <;> simp [h] }

theorem coordinateProjection_apply {j : ℕ} (z : ComplexModel n) (a : Fin j) :
    coordinateProjection n j z a = if h : a.1 < n then z ⟨a.1, h⟩ else 0 := rfl

theorem coordinateInclusion_apply {j : ℕ} (w : ComplexModel j) (i : Fin n) :
    coordinateInclusion n j w i = if h : i.1 < j then w ⟨i.1, h⟩ else 0 := rfl

theorem coordinateProjection_coordinateInclusion {j : ℕ} (hj : j ≤ n) (w : ComplexModel j) :
    coordinateProjection n j (coordinateInclusion n j w) = w := by
  ext a
  have ha : a.1 < n := lt_of_lt_of_le a.2 hj
  simp [coordinateProjection_apply, coordinateInclusion_apply, ha]

theorem coordinateInclusion_mem_complexCoordinatePlane {j : ℕ} (w : ComplexModel j) :
    coordinateInclusion n j w ∈ complexCoordinatePlane n j := by
  intro i hi
  simp [coordinateInclusion_apply, not_lt.mpr hi]

theorem coordinateInclusion_coordinateProjection {j : ℕ} {z : ComplexModel n}
    (hz : z ∈ complexCoordinatePlane n j) :
    coordinateInclusion n j (coordinateProjection n j z) = z := by
  ext i
  by_cases h : i.1 < j
  · simp [coordinateInclusion_apply, coordinateProjection_apply, h, i.2]
  · simp [coordinateInclusion_apply, h, hz i (not_lt.mp h)]

/-! ### Assembling holomorphic coordinates -/

/-- The map `ℂ^n → ℂ^n` with coordinate functions `φ k`. -/
def assemble (φ : Fin n → ComplexModel n → ℂ) (z : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 (fun k => φ k z)

theorem assemble_apply (φ : Fin n → ComplexModel n → ℂ) (z : ComplexModel n) (k : Fin n) :
    assemble φ z k = φ k z := rfl

theorem differentiableOn_assemble {φ : Fin n → ComplexModel n → ℂ} {N : Set (ComplexModel n)}
    (hφ : ∀ k, DifferentiableOn ℂ (φ k) N) : DifferentiableOn ℂ (assemble φ) N := by
  have h : DifferentiableOn ℂ (fun z k => φ k z) N := differentiableOn_pi.mpr hφ
  exact (EuclideanSpace.equiv (Fin n) ℂ).symm.differentiable.comp_differentiableOn h

/-- The differential of a coordinate function is the coordinate of the differential. -/
theorem fderiv_coordinate_eq {F : ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (hF : DifferentiableAt ℂ F z) (k : Fin n) :
    fderiv ℂ (fun y => F y k) z = (EuclideanSpace.proj k).comp (fderiv ℂ F z) := by
  have := ((EuclideanSpace.proj (𝕜 := ℂ) k).hasFDerivAt.comp z hF.hasFDerivAt).fderiv
  exact this

/-! ### Independent vanishing functions -/

/-- `S` is cut out near `q` by at least `R` holomorphic functions with linearly independent
differentials: there are `R` functions holomorphic on an open neighbourhood `N` of `q`,
vanishing on `N ∩ S`, whose differentials at `q` are linearly independent. -/
def HasIndependentVanishing (S : Set (ComplexModel n)) (q : ComplexModel n) (R : ℕ) : Prop :=
  ∃ g : Fin R → ComplexModel n → ℂ, ∃ N : Set (ComplexModel n), IsOpen N ∧ q ∈ N ∧
    (∀ r, DifferentiableOn ℂ (g r) N) ∧ (∀ r, ∀ z ∈ N ∩ S, g r z = 0) ∧
    LinearIndependent ℂ (fun r => fderiv ℂ (g r) q)

theorem finrank_strongDual_complexModel :
    finrank ℂ (ComplexModel n →L[ℂ] ℂ) = n := by
  rw [← LinearEquiv.finrank_eq
    (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ComplexModel n) (F' := ℂ))]
  simp

theorem HasIndependentVanishing.le {S : Set (ComplexModel n)} {q : ComplexModel n} {R : ℕ}
    (h : HasIndependentVanishing S q R) : R ≤ n := by
  obtain ⟨g, -, -, -, -, -, hli⟩ := h
  have := hli.fintype_card_le_finrank
  simpa [finrank_strongDual_complexModel] using this

theorem hasIndependentVanishing_zero (S : Set (ComplexModel n)) (q : ComplexModel n) :
    HasIndependentVanishing S q 0 :=
  ⟨fun r => r.elim0, univ, isOpen_univ, mem_univ q, fun r => r.elim0, fun r => r.elim0,
    linearIndependent_empty_type⟩

/-- A family of functionals vanishing at `v` which spans the dual forces `v = 0`. -/
theorem eq_zero_of_basis_apply_eq_zero {ι : Type*} (b : Basis ι ℂ (ComplexModel n →L[ℂ] ℂ))
    {v : ComplexModel n} (hv : ∀ i, b i v = 0) : v = 0 := by
  have hall : ∀ L : ComplexModel n →L[ℂ] ℂ, L v = 0 := by
    intro L
    rw [← b.linearCombination_repr L, Finsupp.linearCombination_apply, Finsupp.sum]
    simp [hv]
  ext k
  simpa using hall (EuclideanSpace.proj k)

/-- **Completing independent vanishing functions to coordinates.** -/
theorem exists_coordinates_of_linearIndependent {R : ℕ} (hR : R ≤ n)
    {g : Fin R → ComplexModel n → ℂ} {N : Set (ComplexModel n)} (hN : IsOpen N)
    {q : ComplexModel n} (hq : q ∈ N) (hg : ∀ r, DifferentiableOn ℂ (g r) N)
    (hgq : ∀ r, g r q = 0) (hli : LinearIndependent ℂ (fun r => fderiv ℂ (g r) q)) :
    ∃ φ : Fin n → ComplexModel n → ℂ, (∀ k, DifferentiableOn ℂ (φ k) N) ∧
      (∀ k, φ k q = 0) ∧
      (∀ r : Fin R, φ ⟨n - R + r.1, by omega⟩ = g r) ∧
      (∀ z, assemble φ z ∈ complexCoordinatePlane n (n - R) ↔ ∀ r, g r z = 0) ∧
      Function.Injective (fderiv ℂ (assemble φ) q) := by
  classical
  obtain ⟨κ, _, b, hbinl⟩ : ∃ (κ : Type) (_ : Fintype κ)
      (b : Basis (Fin R ⊕ κ) ℂ (ComplexModel n →L[ℂ] ℂ)),
      ∀ r, b (Sum.inl r) = fderiv ℂ (g r) q := by
    have hfin := Module.Finite.finite_basis (Basis.sumExtend hli)
    have : Finite (Basis.sumExtendIndex hli) := Finite.of_injective (β := Fin R ⊕
      Basis.sumExtendIndex hli) Sum.inr Sum.inr_injective
    refine ⟨_, Fintype.ofFinite _, Basis.sumExtend hli, fun r => ?_⟩
    simp only [Basis.sumExtend, Basis.reindex_apply, Basis.coe_extend]
    rfl
  have hcard : Fintype.card κ = n - R := by
    have := finrank_eq_card_basis b
    rw [finrank_strongDual_complexModel, Fintype.card_sum, Fintype.card_fin] at this
    omega
  set e : κ ≃ Fin (n - R) := Fintype.equivFinOfCardEq hcard
  let ℓ : Fin (n - R) → ComplexModel n →L[ℂ] ℂ := fun a => b (Sum.inr (e.symm a))
  let φ : Fin n → ComplexModel n → ℂ := fun k =>
    if h : k.1 < n - R then fun z => ℓ ⟨k.1, h⟩ (z - q) else g ⟨k.1 - (n - R), by omega⟩
  have hφg : ∀ r : Fin R, φ ⟨n - R + r.1, by omega⟩ = g r := by
    intro r
    simp only [φ, show ¬ (n - R + r.1 < n - R) by omega, dite_eq_right, not_false_eq_true]
    congr 1
    ext
    simp
  have hφd : ∀ k, DifferentiableOn ℂ (φ k) N := by
    intro k
    by_cases h : k.1 < n - R
    · simp only [φ, dite_eq_left h]
      exact ((ℓ ⟨k.1, h⟩).differentiable.comp (differentiable_id.sub_const q)).differentiableOn
    · simp only [φ, dite_eq_right h]
      exact hg _
  refine ⟨φ, hφd, ?_, hφg, ?_, ?_⟩
  · intro k
    by_cases h : k.1 < n - R
    · simp [φ, h]
    · simp only [φ, dite_eq_right h]
      exact hgq _
  · intro z
    constructor
    · intro hz r
      have := hz ⟨n - R + r.1, by omega⟩ (by simp)
      rwa [assemble_apply, hφg] at this
    · intro hz k hk
      rw [assemble_apply]
      simp only [φ, dite_eq_right (not_lt.mpr hk)]
      exact hz _
  · have hAd : DifferentiableAt ℂ (assemble φ) q :=
      (differentiableOn_assemble hφd).differentiableAt (hN.mem_nhds hq)
    refine (injective_iff_map_eq_zero (fderiv ℂ (assemble φ) q)).mpr ?_
    intro v hv
    have hcoord : ∀ k, fderiv ℂ (φ k) q v = 0 := by
      intro k
      have h1 := fderiv_coordinate_eq hAd k
      have h2 : (fun y => assemble φ y k) = φ k := rfl
      rw [h2] at h1
      rw [h1]
      simp [hv]
    refine eq_zero_of_basis_apply_eq_zero b ?_
    rintro (r | c)
    · rw [hbinl, ← hφg r]
      exact hcoord _
    · have hk : (e c).1 < n - R := (e c).2
      have := hcoord ⟨(e c).1, by omega⟩
      simp only [φ, dite_eq_left hk] at this
      have hfd : fderiv ℂ (fun z => ℓ ⟨(e c).1, hk⟩ (z - q)) q = ℓ ⟨(e c).1, hk⟩ := by
        have := ((ℓ ⟨(e c).1, hk⟩).hasFDerivAt.comp q
          ((hasFDerivAt_id q).sub_const q)).fderiv
        exact this
      rw [hfd] at this
      simpa [ℓ] using this

/-- Linear independence of the differentials produced in the maximality argument. -/
theorem linearIndependent_snoc_coordinates {R : ℕ} (hR : R ≤ n)
    {A : ComplexModel n →L[ℂ] ComplexModel n} (hA : Function.Injective A)
    {L : ComplexModel (n - R) →L[ℂ] ℂ} (hL : L ≠ 0) :
    LinearIndependent ℂ (Fin.snoc (α := fun _ => ComplexModel n →L[ℂ] ℂ)
      (fun r : Fin R => (EuclideanSpace.proj (𝕜 := ℂ) (⟨n - R + r.1, by omega⟩ : Fin n)).comp A)
      ((L.comp (coordinateProjection n (n - R))).comp A)) := by
  classical
  have hAsurj : Function.Surjective A :=
    LinearMap.injective_iff_surjective.mp hA
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hval : ∀ t : ComplexModel n,
      (∑ r : Fin R, c r.castSucc * t ⟨n - R + r.1, by omega⟩) +
        c (Fin.last R) * L (coordinateProjection n (n - R) t) = 0 := by
    intro t
    obtain ⟨u, rfl⟩ := hAsurj t
    have := congrArg (fun F : ComplexModel n →L[ℂ] ℂ => F u) hc
    simpa [Fin.sum_univ_castSucc] using this
  have hlast : c (Fin.last R) = 0 := by
    obtain ⟨w, hw⟩ : ∃ w, L w ≠ 0 := by
      by_contra h
      push Not at h
      exact hL (ContinuousLinearMap.ext h)
    have := hval (coordinateInclusion n (n - R) w)
    rw [coordinateProjection_coordinateInclusion (Nat.sub_le n R)] at this
    have hz : ∀ r : Fin R, coordinateInclusion n (n - R) w ⟨n - R + r.1, by omega⟩ = 0 :=
      fun r => coordinateInclusion_mem_complexCoordinatePlane w _ (by simp)
    simp only [hz, mul_zero, Finset.sum_const_zero, zero_add, mul_eq_zero] at this
    exact this.resolve_right hw
  intro i
  refine Fin.lastCases hlast (fun r => ?_) i
  have := hval (EuclideanSpace.single (⟨n - R + r.1, by omega⟩ : Fin n) 1)
  have hproj : coordinateProjection n (n - R)
      (EuclideanSpace.single (⟨n - R + r.1, by omega⟩ : Fin n) (1 : ℂ)) = 0 := by
    ext a
    simp only [coordinateProjection_apply]
    split_ifs with h
    · rw [PiLp.single_apply]
      simp only [Fin.mk.injEq]
      rw [ite_eq_right (by omega)]
      simp
    · simp
  rw [hproj, map_zero, mul_zero, add_zero] at this
  rw [Finset.sum_eq_single r] at this
  · simpa using this
  · intro r' _ hr'
    rw [PiLp.single_apply, ite_eq_right]
    · simp
    · simp only [Fin.mk.injEq]
      intro h
      exact hr' (Fin.ext (by omega))
  · simp

/-! ### Density in coordinates -/

/-- **Regular points are dense in a zero locus (coordinate form).**  If `S` is the common
zero set in the open set `W ⊆ ℂ^n` of finitely many holomorphic functions, then every open
set `U` meeting `S ∩ W` contains a point `q ∈ S ∩ W` near which `S` is biholomorphically
flattened onto a coordinate plane. -/
theorem exists_flattening_of_isZeroLocus {S W U : Set (ComplexModel n)} (hW : IsOpen W)
    (hU : IsOpen U) {m : ℕ} {f : Fin m → ComplexModel n → ℂ}
    (hf : ∀ i, DifferentiableOn ℂ (f i) W) (hS : ∀ z ∈ W, z ∈ S ↔ ∀ i, f i z = 0)
    {q₀ : ComplexModel n} (hq₀S : q₀ ∈ S) (hq₀W : q₀ ∈ W) (hq₀U : q₀ ∈ U) :
    ∃ q ∈ S ∩ W ∩ U, ∃ j ≤ n, ∃ Φ : LocalHolomorphicEquivAt (n := n) q,
      Φ.source ⊆ W ∩ U ∧ Φ.toFun q = 0 ∧
      ∀ z ∈ Φ.source, (z ∈ S ↔ Φ.toFun z ∈ complexCoordinatePlane n j) := by
  classical
  let P : ℕ → Prop := fun R => ∃ q ∈ S ∩ W ∩ U, HasIndependentVanishing S q R
  have hP0 : P 0 := ⟨q₀, ⟨⟨hq₀S, hq₀W⟩, hq₀U⟩, hasIndependentVanishing_zero S q₀⟩
  set R := Nat.findGreatest P n with hRdef
  have hRn : R ≤ n := Nat.findGreatest_le n
  have hmax : ¬ P (R + 1) := by
    rintro ⟨q, hq, hind⟩
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self R) hind.le ⟨q, hq, hind⟩
  obtain ⟨q, hqT, g, N₀, hN₀, hqN₀, hg, hgS, hli⟩ : P R := Nat.findGreatest_spec (Nat.zero_le n)
    hP0
  obtain ⟨φ, hφd, hφ0, hφg, hφplane, hinj⟩ := exists_coordinates_of_linearIndependent hRn hN₀
    hqN₀ hg (fun r => hgS r q ⟨hqN₀, hqT.1.1⟩) hli
  set j := n - R with hj
  have hN : IsOpen (N₀ ∩ W ∩ U) := (hN₀.inter hW).inter hU
  obtain ⟨Φ, hΦN, hΦF, hΦinj⟩ := exists_localHolomorphicEquivAt hN ⟨⟨hqN₀, hqT.1.2⟩, hqT.2⟩
    ((differentiableOn_assemble hφd).mono fun z hz => hz.1.1) hinj
  have hΦq : Φ.toFun q = 0 := by
    rw [hΦF]
    ext k
    simp [assemble_apply, hφ0]
  have hflatS : ∀ z ∈ Φ.source, z ∈ S → Φ.toFun z ∈ complexCoordinatePlane n j := by
    intro z hz hzS
    rw [hΦF, hφplane]
    exact fun r => hgS r z ⟨(hΦN hz).1.1, hzS⟩
  set ι := coordinateInclusion n j with hι
  set π := coordinateProjection n j with hπ
  set Ω : Set (ComplexModel j) := ι ⁻¹' Φ.target with hΩdef
  have hΩ : IsOpen Ω := Φ.isOpen_target.preimage ι.continuous
  have h0Ω : (0 : ComplexModel j) ∈ Ω := by
    change ι 0 ∈ Φ.target
    rw [map_zero, ← hΦq]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  have hinvN : ∀ w ∈ Ω, Φ.invFun (ι w) ∈ N₀ ∩ W ∩ U := fun w hw => hΦN (Φ.mapsTo_invFun hw)
  let h : Fin m → ComplexModel j → ℂ := fun i w => f i (Φ.invFun (ι w))
  have hh : ∀ i, DifferentiableOn ℂ (h i) Ω := fun i =>
    (hf i).comp (Φ.invFun_holomorphic.comp ι.differentiable.differentiableOn fun w hw => hw)
      fun w hw => (hinvN w hw).1.2
  have hhS : ∀ w ∈ Ω, Φ.invFun (ι w) ∈ S ↔ ∀ i, h i w = 0 :=
    fun w hw => hS _ (hinvN w hw).1.2
  have hinv0 : Φ.invFun (ι 0) = q := by
    rw [map_zero, ← hΦq, Φ.left_inv q Φ.center_mem_source]
  have hπΦ : ∀ z ∈ Φ.source, z ∈ S → Φ.invFun (ι (π (Φ.toFun z))) = z ∧
      π (Φ.toFun z) ∈ Ω := by
    intro z hz hzS
    have hιw : ι (π (Φ.toFun z)) = Φ.toFun z :=
      coordinateInclusion_coordinateProjection (hflatS z hz hzS)
    refine ⟨by rw [hιw, Φ.left_inv z hz], ?_⟩
    change ι (π (Φ.toFun z)) ∈ Φ.target
    rw [hιw]
    exact Φ.mapsTo_toFun hz
  by_cases hall : ∀ i, h i =ᶠ[𝓝 0] 0
  · -- all `h i` vanish near `0`: `S` is flattened near `q`
    have hev : ∀ᶠ w in 𝓝 (0 : ComplexModel j), ∀ i, h i w = 0 := eventually_all.mpr hall
    obtain ⟨O, hOsub, hO, h0O⟩ := mem_nhds_iff.mp hev
    set s := Φ.source ∩ Φ.toFun ⁻¹' (π ⁻¹' O) with hsdef
    have hs : IsOpen s :=
      Φ.toFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_source
        (hO.preimage π.continuous)
    have hqs : q ∈ Φ.source ∩ s := by
      refine ⟨Φ.center_mem_source, Φ.center_mem_source, ?_⟩
      change π (Φ.toFun q) ∈ O
      rw [hΦq, map_zero]
      exact h0O
    refine ⟨q, hqT, j, Nat.sub_le n R, Φ.restrict s hs q hqs, ?_, by simpa using hΦq, ?_⟩
    · intro z hz
      exact ⟨(hΦN hz.1).1.2, (hΦN hz.1).2⟩
    · intro z hz
      simp only [LocalHolomorphicEquivAt.restrict_toFun]
      refine ⟨hflatS z hz.1, fun hplane => ?_⟩
      have hιw : ι (π (Φ.toFun z)) = Φ.toFun z :=
        coordinateInclusion_coordinateProjection hplane
      have hwΩ : π (Φ.toFun z) ∈ Ω := by
        change ι (π (Φ.toFun z)) ∈ Φ.target
        rw [hιw]
        exact Φ.mapsTo_toFun hz.1
      have hzinv : Φ.invFun (ι (π (Φ.toFun z))) = z := by rw [hιw, Φ.left_inv z hz.1]
      rw [← hzinv]
      exact (hhS _ hwΩ).mpr (hOsub hz.2.2)
  · -- some `h i` does not vanish near `0`: contradiction with maximality of `R`
    exfalso
    push Not at hall
    obtain ⟨i₀, hi₀⟩ := hall
    set Z : Set (ComplexModel j) := {w | w ∈ Ω ∧ Φ.invFun (ι w) ∈ S} with hZdef
    obtain ⟨G, hG, hGZ, w', hw'Z, hGw'⟩ := exists_fderiv_ne_zero_of_not_eventuallyEq_zero (Z := Z)
      hΩ
      (fun w hw => hw.1) (hh i₀) (fun w hw => (hhS w hw.1).mp hw.2 i₀)
      ⟨h0Ω, by rw [hinv0]; exact hqT.1.1⟩ hi₀
    apply hmax
    set q' := Φ.invFun (ι w') with hq'def
    have hq'src : q' ∈ Φ.source := Φ.mapsTo_invFun hw'Z.1
    have hΦq' : Φ.toFun q' = ι w' := Φ.right_inv _ hw'Z.1
    have hπι : π (ι w') = w' := coordinateProjection_coordinateInclusion (Nat.sub_le n R) w'
    set N' := Φ.source ∩ Φ.toFun ⁻¹' (π ⁻¹' Ω) with hN'def
    have hN' : IsOpen N' :=
      Φ.toFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_source
        (hΩ.preimage π.continuous)
    have hq'N' : q' ∈ N' := by
      refine ⟨hq'src, ?_⟩
      change π (Φ.toFun q') ∈ Ω
      rw [hΦq', hπι]
      exact hw'Z.1
    have hN'N₀ : N' ⊆ N₀ := fun z hz => (hΦN hz.1).1.1
    let G' : ComplexModel n → ℂ := fun z => G (π (Φ.toFun z))
    have hG'd : DifferentiableOn ℂ G' N' :=
      hG.comp ((π.differentiable.differentiableOn (s := univ)).comp
        (Φ.toFun_holomorphic.mono inter_subset_left) (mapsTo_univ _ _)) fun z hz => hz.2
    have hAd : DifferentiableAt ℂ (assemble φ) q' :=
      (differentiableOn_assemble hφd).differentiableAt (hN₀.mem_nhds (hN'N₀ hq'N'))
    set A := fderiv ℂ (assemble φ) q' with hAdef
    refine ⟨q', ⟨⟨hw'Z.2, (hΦN hq'src).1.2⟩, (hΦN hq'src).2⟩,
      Fin.snoc (α := fun _ => ComplexModel n → ℂ) g G', N', hN', hq'N', ?_, ?_, ?_⟩
    · intro r
      refine Fin.lastCases ?_ (fun r => ?_) r
      · simpa using hG'd
      · simpa using (hg r).mono hN'N₀
    · intro r
      refine Fin.lastCases ?_ (fun r => ?_) r
      · intro z hz
        simp only [Fin.snoc_last]
        obtain ⟨hzinv, hzΩ⟩ := hπΦ z hz.1.1 hz.2
        exact hGZ _ ⟨hzΩ, by rw [hzinv]; exact hz.2⟩
      · intro z hz
        simp only [Fin.snoc_castSucc]
        exact hgS r z ⟨hN'N₀ hz.1, hz.2⟩
    · -- the differentials at `q'`
      have hinjA : Function.Injective A := hΦinj q' hq'src
      have hdg : ∀ r : Fin R, fderiv ℂ (g r) q' =
          (EuclideanSpace.proj (𝕜 := ℂ) (⟨n - R + r.1, by omega⟩ : Fin n)).comp A := by
        intro r
        rw [← hφg r]
        exact fderiv_coordinate_eq hAd _
      have hdG' : fderiv ℂ G' q' = ((fderiv ℂ G w').comp π).comp A := by
        have hGd : DifferentiableAt ℂ G w' := hG.differentiableAt (hΩ.mem_nhds hw'Z.1)
        have hπA : HasFDerivAt (fun z => π (assemble φ z)) (π.comp A) q' :=
          π.hasFDerivAt.comp q' hAd.hasFDerivAt
        have hπq' : π (assemble φ q') = w' := by rw [← hΦF, hΦq', hπι]
        have hGd' : HasFDerivAt G (fderiv ℂ G w') (π (assemble φ q')) := by
          rw [hπq']
          exact hGd.hasFDerivAt
        have hG'eq : G' = fun z => G (π (assemble φ z)) := by simp only [G', hΦF]
        rw [hG'eq, ContinuousLinearMap.comp_assoc]
        exact (hGd'.comp q' hπA).fderiv
      have hfam : (fun r : Fin (R + 1) =>
          fderiv ℂ (Fin.snoc (α := fun _ => ComplexModel n → ℂ) g G' r) q') =
          Fin.snoc (α := fun _ => ComplexModel n →L[ℂ] ℂ)
            (fun r : Fin R =>
              (EuclideanSpace.proj (𝕜 := ℂ) (⟨n - R + r.1, by omega⟩ : Fin n)).comp A)
            (((fderiv ℂ G w').comp π).comp A) := by
        funext r
        refine Fin.lastCases ?_ (fun r => ?_) r
        · simpa using hdG'
        · simpa using hdg r
      rw [hfam]
      exact linearIndependent_snoc_coordinates hRn hinjA hGw'

/-! ### Density on manifolds -/

section Manifold

open RegularPatchNeighborhood

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- `RegularPatchNeighborhood.regularAtDim_of_flattening` for a flattening `Φ` of `A`, in the
preferred chart at `x`, centred at an arbitrary point. -/
theorem regularAtDim_of_flattening_of_mem {A : Set M} {x y : M} {k : ℕ} (hk : k ≤ n)
    {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p)
    (hflat : ∀ {y : M},
      y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ A ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n k))
    (hyA : y ∈ A) (hy : y ∈ (complexChartAt (n := n) x).val.source)
    (hyΦ : (complexChartAt (n := n) x).val y ∈ Φ.source) :
    RegularAtDim (n := n) A y k :=
  RegularPatchNeighborhood.regularAtDim_of_flattening_of_mem (x := x) hk Φ hflat hyA hy hyΦ

/-- **The regular locus of an analytic subset is dense.**  Every neighbourhood of a point of
an analytic subset `A` contains a point at which `A` is regular of some dimension. -/
theorem exists_regularAtDim_mem_nhds {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    {x : M} (hx : x ∈ A) {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ y ∈ U, ∃ k, RegularAtDim (n := n) A y k := by
  obtain ⟨pres⟩ := hA x
  set e := (complexChartAt (n := n) x).val with he
  have hxe : x ∈ e.source := mem_complexChartAt_source x
  let S : Set (ComplexModel n) := {z | e.symm z ∈ A}
  obtain ⟨U₀, hU₀U, hU₀, hxU₀⟩ := mem_nhds_iff.mp hU
  have hU' : IsOpen (e.target ∩ e.symm ⁻¹' U₀) :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target hU₀
  have hS : ∀ z ∈ pres.coordinateNeighborhood, z ∈ S ↔ ∀ i, pres.generator i z = 0 := by
    intro z hz
    have hzt := pres.coordinateNeighborhood_subset_target hz
    have := pres.zeroLocus (e.map_target hzt) (by rwa [e.right_inv hzt])
    rwa [e.right_inv hzt] at this
  have hexU : e x ∈ e.target ∩ e.symm ⁻¹' U₀ :=
    ⟨e.map_source hxe, by simpa [mem_preimage, e.left_inv hxe] using hxU₀⟩
  have hexS : e x ∈ S := by simpa [S, e.left_inv hxe] using hx
  obtain ⟨q, ⟨⟨hqS, -⟩, hqU⟩, j, hj, Φ, -, -, hΦflat⟩ :=
    exists_flattening_of_isZeroLocus pres.isOpen_coordinateNeighborhood hU'
      pres.generator_holomorphic hS hexS pres.center_mem_coordinateNeighborhood hexU
  refine ⟨e.symm q, hU₀U hqU.2, j, ?_⟩
  refine regularAtDim_of_flattening_of_mem hj Φ ?_ hqS (e.map_target hqU.1)
    (by rw [e.right_inv hqU.1]; exact Φ.center_mem_source)
  intro y hy hyΦ
  have := hΦflat (e y) hyΦ
  simpa [S, e.left_inv hy] using this

/-- An analytic subset lies in the closure of its regular locus. -/
theorem subset_closure_iUnion_regularLocus {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) :
    A ⊆ closure (⋃ k, regularLocus (n := n) A k) := by
  intro x hx
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨y, hyU, k, hy⟩ := exists_regularAtDim_mem_nhds hA hx hU
  exact ⟨y, hyU, mem_iUnion.mpr ⟨k, hy⟩⟩

/-- A relatively open nonempty part of an analytic subset contains a regular point: if
`y ∈ A` lies in the open set `O`, then `A` is regular of some dimension at a point of `O`. -/
theorem exists_regularAtDim_mem_of_isOpen {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    {O : Set M} (hO : IsOpen O) {y : M} (hyA : y ∈ A) (hyO : y ∈ O) :
    ∃ x ∈ O, ∃ k, RegularAtDim (n := n) A x k :=
  exists_regularAtDim_mem_nhds hA hyA (hO.mem_nhds hyO)

end Manifold

end

end SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
