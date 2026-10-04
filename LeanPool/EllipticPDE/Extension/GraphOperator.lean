/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Extension.LinearOperator
public import LeanPool.EllipticPDE.Extension.GlobalApproximation
public import LeanPool.EllipticPDE.Embedding.H01Sobolev


/-!
# Extension operator between the graph spaces

`EllipticPdes.Extension.exists_extLinear` is the extension operator on pairs of a class and its
gradient, given as functions. Guo's Theorem III.2.2 states it as a bounded linear map
`E : W^{1,p}(Ω) → W^{1,p}(ℝⁿ)` between the Sobolev spaces. This file states it that way at
`p = 2`, between the graph spaces `W12 Ω` and `W12 ℝᵈ` of this development.

The passage from functions to classes needs nothing beyond the bound. A linear map on
representatives whose image is bounded in `L²(ℝᵈ)` by the `L²(Ω)` seminorms of the input
descends to classes: two representatives of one class differ by a pair of seminorm zero, so
their images differ by a function of seminorm zero, which vanishes almost everywhere. The map
is then linear on the classes, bounded by the same constant, its image lies in the graph space
of the whole space because the image pair has a weak gradient there, and the three clauses of
the theorem are read off `exists_extLinear` through the representatives.

## Main declarations

* `EllipticPdes.Extension.mem_W12_of_hasWeakGradOn`: a class with an `L²` weak gradient,
  paired with it, lies in the graph space.
* `EllipticPdes.Extension.exists_extW12`: the extension operator as a bounded linear map
  between the graph spaces, with the three clauses of Guo III.2.2.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.2.2
(p. 20); L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4 Theorem 1 (p. 253).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev
open EllipticPdes.Embedding (HasWeakGradOn hasWeakGradOn_zero hasWeakGradOn_unique_ae
  isFiniteMeasure_restrict_of_isBounded norm_apply_le)

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- Almost everywhere for the restriction to the whole space is almost everywhere. -/
theorem ae_of_ae_restrict_univ {p : EuclideanSpace ℝ (Fin d) → Prop}
    (h : ∀ᵐ x ∂(volume.restrict (Set.univ : Set (EuclideanSpace ℝ (Fin d)))), p x) :
    ∀ᵐ x ∂volume, p x :=
  ((ae_restrict_iff' MeasurableSet.univ).mp h).mono fun x hx => hx (mem_univ x)

/-! ### Membership of a pair in the graph space -/

/-- **Membership of a class with an `L²` weak gradient in the graph space**, paired with that
gradient.
This is the converse of `hasWeakGradOn_of_mem_W12`: the constraint defining `W12 Ω` is the
integration by parts the weak gradient asserts. -/
theorem mem_W12_of_hasWeakGradOn {F : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hF : MemLp F 2 (volume.restrict Ω))
    (hG : ∀ k, MemLp (G k) 2 (volume.restrict Ω)) (hwg : HasWeakGradOn Ω F G) :
    (WithLp.toLp 2 (Fin.cons (hF.toLp F) fun k => (hG k).toLp (G k)) : H1amb Ω) ∈ W12 Ω := by
  rw [mem_W12_iff]
  intro φ h i
  simp only [Fin.cons_zero, Fin.cons_succ, IsTestFn.partialCls, IsTestFn.testCls]
  rw [inner_toLp_eq, inner_toLp_eq]
  have key := hwg φ h.1 h.2.1 h.2.2 i
  have e1 : ∫ x in Ω, partialD i φ x * F x = ∫ x in Ω, F x * partialD i φ x :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have e2 : ∫ x in Ω, φ x * G i x = ∫ x in Ω, G i x * φ x :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [e1, e2, key]
  ring

/-! ### The operator on the graph spaces -/

private lemma extension_pair_congr_ae : ∀ {d : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))} (T :
  SobolevPair d →ₗ[ℝ] SobolevPair d)
  (K : ℝ≥0)
  (_ :
    ∀ (w : SobolevPair d),
      IntegrableOn w.1 Ω volume →
        (∀ (k : Fin d), IntegrableOn (w.2 k) Ω volume) →
          HasWeakGradOn Ω w.1 w.2 →
            HasWeakGradOn univ (T w).1 (T w).2 ∧
              HasCompactSupport (T w).1 ∧
                tsupport (T w).1 ⊆ Ω' ∧
                  Integrable (T w).1 volume ∧
                    (∀ (k : Fin d), Integrable ((T w).2 k) volume) ∧
                      (∀ y ∈ Ω, (T w).1 y = w.1 y) ∧
                        eLpNorm (T w).1 2 volume ≤
                            ↑K * (eLpNorm w.1 2 (volume.restrict Ω) + ∑ i, eLpNorm (w.2 i) 2
                              (volume.restrict Ω)) ∧
                          ∀ (k : Fin d),
                            eLpNorm ((T w).2 k) 2 volume ≤
                              ↑K * (eLpNorm w.1 2 (volume.restrict Ω) + ∑ i, eLpNorm (w.2 i) 2
                                (volume.restrict Ω)))
  (p q : SobolevPair d),
  IntegrableOn p.1 Ω volume →
    (∀ (k : Fin d), IntegrableOn (p.2 k) Ω volume) →
      HasWeakGradOn Ω p.1 p.2 →
        IntegrableOn q.1 Ω volume →
          (∀ (k : Fin d), IntegrableOn (q.2 k) Ω volume) →
            HasWeakGradOn Ω q.1 q.2 →
              p.1 =ᵐ[volume.restrict Ω] q.1 →
                (∀ (k : Fin d), p.2 k =ᵐ[volume.restrict Ω] q.2 k) →
                  (T p).1 =ᵐ[volume] (T q).1 ∧ ∀ (k : Fin d), (T p).2 k =ᵐ[volume] (T q).2 k := by
  classical
  intro d Ω Ω' T K hT p q hp1 hp2 hpw hq1 hq2 hqw h1 h2
  have hd1 : (p - q).1 =ᵐ[volume.restrict Ω] (0 : EuclideanSpace ℝ (Fin d) → ℝ) := by
    filter_upwards [h1] with x hx
    simp only [Prod.fst_sub, Pi.sub_apply, hx, sub_self, Pi.zero_apply]
  have hd2 : ∀ k, (p - q).2 k =ᵐ[volume.restrict Ω] (0 : EuclideanSpace ℝ (Fin d) → ℝ) := by
    intro k
    filter_upwards [h2 k] with x hx
    simp only [Prod.snd_sub, Pi.sub_apply, hx, sub_self, Pi.zero_apply]
  have hdw : HasWeakGradOn Ω (p - q).1 (p - q).2 :=
    hasWeakGradOn_zero.congr_ae hd1.symm fun k => (hd2 k).symm
  obtain ⟨-, -, -, hint, hgint, -, hb1, hb2⟩ :=
    hT (p - q) (hp1.sub hq1) (fun k => (hp2 k).sub (hq2 k)) hdw
  have hzero : eLpNorm (p - q).1 2 (volume.restrict Ω)
      + ∑ i, eLpNorm ((p - q).2 i) 2 (volume.restrict Ω) = 0 := by
    rw [eLpNorm_congr_ae hd1, eLpNorm_zero, zero_add]
    exact Finset.sum_eq_zero fun i _ => by rw [eLpNorm_congr_ae (hd2 i), eLpNorm_zero]
  rw [hzero, mul_zero, nonpos_iff_eq_zero] at hb1
  have hb2' : ∀ k, eLpNorm ((T (p - q)).2 k) 2 volume = 0 := fun k => by
    have := hb2 k
    rwa [hzero, mul_zero, nonpos_iff_eq_zero] at this
  have e1 : (T (p - q)).1 = (T p).1 - (T q).1 := by rw [map_sub]; rfl
  have e2 : ∀ k, (T (p - q)).2 k = (T p).2 k - (T q).2 k := fun k => by rw [map_sub]; rfl
  refine ⟨?_, fun k => ?_⟩
  · have h := (eLpNorm_eq_zero_iff two_ne_zero).mp hb1
    rw [e1] at h
    filter_upwards [h] with x hx
    simpa [sub_eq_zero] using hx
  · have h := (eLpNorm_eq_zero_iff two_ne_zero).mp (hb2' k)
    rw [e2 k] at h
    filter_upwards [h] with x hx
    simpa [sub_eq_zero] using hx


private lemma graph_coordinate_norm_sum_le : ∀ {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))},
  let w := fun U : W12 Ω => (fun x => ((U : H1amb Ω) 0 : L2D Ω) x, fun (k : Fin d) x => ((U :
    H1amb Ω)
    k.succ : L2D Ω) x);
  ∀ (U : ↥(W12 Ω)),
    eLpNorm (w U).1 2 (volume.restrict Ω) + ∑ i, eLpNorm ((w U).2 i) 2 (volume.restrict Ω) ≤
      ENNReal.ofReal ((↑d + 1) * ‖U‖) := by
  classical
  intro d Ω w U
  have h0 : eLpNorm (w U).1 2 (volume.restrict Ω) = ENNReal.ofReal ‖(U : H1amb Ω) 0‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top _).ne]
  have hk : ∀ k : Fin d, eLpNorm ((w U).2 k) 2 (volume.restrict Ω)
      = ENNReal.ofReal ‖(U : H1amb Ω) k.succ‖ := fun k => by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top _).ne]
  rw [h0]
  simp_rw [hk]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _),
    ← ENNReal.ofReal_add (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hU : ‖U‖ = ‖(U : H1amb Ω)‖ := rfl
  calc ‖(U : H1amb Ω) 0‖ + ∑ k : Fin d, ‖(U : H1amb Ω) k.succ‖
      ≤ ‖U‖ + ∑ _k : Fin d, ‖U‖ := by
        rw [hU]
        exact add_le_add (norm_apply_le _ _) (Finset.sum_le_sum fun k _ => norm_apply_le _ _)
    _ = (d + 1) * ‖U‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **Extension operator between the graph spaces** (Guo Theorem III.2.2 at `p = 2`,
Evans §5.4 Theorem 1). On a bounded open domain with `C¹` boundary, and for any open set
the closure of the domain sits in, there is a bounded linear map from `W12 Ω`, the `H¹(Ω)`
of this development, to the graph space of the whole space, such that the image of every
element agrees with it on the domain, function coordinate and gradient coordinates alike,
its function coordinate vanishes almost everywhere outside the given open set, and it is
bounded by a constant times the norm of the element. -/
theorem exists_extW12 (hd : 0 < d) (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) {Ω' : Set (EuclideanSpace ℝ (Fin d))} (hΩ'open : IsOpen Ω')
    (hsub : closure Ω ⊆ Ω') :
    ∃ (E : W12 Ω →L[ℝ] W12 (Set.univ : Set (EuclideanSpace ℝ (Fin d)))) (C : ℝ),
      (∀ U : W12 Ω,
        (((E U : W12 (Set.univ : Set (EuclideanSpace ℝ (Fin d)))) : H1amb Set.univ) 0 :
            EuclideanSpace ℝ (Fin d) → ℝ)
          =ᵐ[volume.restrict Ω] (fun x => ((U : H1amb Ω) 0 : L2D Ω) x) ∧
        ∀ k : Fin d,
          (((E U : W12 (Set.univ : Set (EuclideanSpace ℝ (Fin d)))) : H1amb Set.univ) k.succ :
              EuclideanSpace ℝ (Fin d) → ℝ)
            =ᵐ[volume.restrict Ω] (fun x => ((U : H1amb Ω) k.succ : L2D Ω) x)) ∧
      (∀ U : W12 Ω, ∀ᵐ y ∂volume, y ∉ Ω' →
        (((E U : W12 (Set.univ : Set (EuclideanSpace ℝ (Fin d)))) : H1amb Set.univ) 0 :
          EuclideanSpace ℝ (Fin d) → ℝ) y = 0) ∧
      ∀ U : W12 Ω, ‖E U‖ ≤ C * ‖U‖ := by
  classical
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict_of_isBounded hΩb
  obtain ⟨T, K, hT⟩ := exists_extLinear hd hΩopen hΩb hC1 hΩ'open hsub (p := 2) one_le_two
  -- the pair an element of the graph space presents to the operator
  let w : W12 Ω → SobolevPair d := fun U =>
    (fun x => ((U : H1amb Ω) 0 : L2D Ω) x, fun (k : Fin d) x => ((U : H1amb Ω) k.succ : L2D Ω) x)
  have hwi : ∀ U : W12 Ω, IntegrableOn (w U).1 Ω volume := fun U =>
    (Lp.memLp _).integrable one_le_two
  have hwgi : ∀ U : W12 Ω, ∀ k, IntegrableOn ((w U).2 k) Ω volume := fun U k =>
    (Lp.memLp _).integrable one_le_two
  have hwg : ∀ U : W12 Ω, HasWeakGradOn Ω (w U).1 (w U).2 := fun U =>
    hasWeakGradOn_of_mem_W12 U.2
  -- the class of the image depends on the class of the input alone
  have hN : ∀ U : W12 Ω, eLpNorm (w U).1 2 (volume.restrict Ω)
      + ∑ i, eLpNorm ((w U).2 i) 2 (volume.restrict Ω) ≤ ENNReal.ofReal ((d + 1) * ‖U‖) := by
    exact graph_coordinate_norm_sum_le
  have hKfin : ∀ U : W12 Ω, (K : ℝ≥0∞) * (eLpNorm (w U).1 2 (volume.restrict Ω)
      + ∑ i, eLpNorm ((w U).2 i) 2 (volume.restrict Ω)) < ⊤ := fun U =>
    ENNReal.mul_lt_top ENNReal.coe_lt_top (lt_of_le_of_lt (hN U) ENNReal.ofReal_lt_top)
  have hspec := fun U : W12 Ω => hT (w U) (hwi U) (hwgi U) (hwg U)
  have hMF : ∀ U : W12 Ω, MemLp (T (w U)).1 2 volume := fun U =>
    lt_of_le_of_lt (hspec U).2.2.2.2.2.2.1 (hKfin U)
  have hMG : ∀ U : W12 Ω, ∀ k, MemLp ((T (w U)).2 k) 2 volume := fun U k =>
    lt_of_le_of_lt ((hspec U).2.2.2.2.2.2.2 k) (hKfin U)
  -- a pair of seminorm zero on the domain has an image of seminorm zero
  have hcongr : ∀ (p q : SobolevPair d), IntegrableOn p.1 Ω volume →
      (∀ k, IntegrableOn (p.2 k) Ω volume) → HasWeakGradOn Ω p.1 p.2 →
      IntegrableOn q.1 Ω volume → (∀ k, IntegrableOn (q.2 k) Ω volume) →
      HasWeakGradOn Ω q.1 q.2 →
      p.1 =ᵐ[volume.restrict Ω] q.1 → (∀ k, p.2 k =ᵐ[volume.restrict Ω] q.2 k) →
      (T p).1 =ᵐ[volume] (T q).1 ∧ ∀ k, (T p).2 k =ᵐ[volume] (T q).2 k := by
    exact extension_pair_congr_ae T K hT
  -- the classes of the image, on the whole space
  have hMF' : ∀ U : W12 Ω, MemLp (T (w U)).1 2 (volume.restrict Set.univ) := fun U => by
    rw [Measure.restrict_univ]; exact hMF U
  have hMG' : ∀ U : W12 Ω, ∀ k, MemLp ((T (w U)).2 k) 2 (volume.restrict Set.univ) :=
    fun U k => by rw [Measure.restrict_univ]; exact hMG U k
  let Eg : W12 Ω → H1amb (Set.univ : Set (EuclideanSpace ℝ (Fin d))) := fun U =>
    WithLp.toLp 2 (Fin.cons ((hMF' U).toLp _) fun k => (hMG' U k).toLp _)
  have hEg0 : ∀ U, (Eg U) 0 = (hMF' U).toLp _ := fun U => by
    simp only [Eg, Fin.cons_zero]
  have hEgk : ∀ U k, (Eg U) (Fin.succ k) = (hMG' U k).toLp _ := fun U k => by
    simp only [Eg, Fin.cons_succ]
  -- the representatives of a sum and of a scalar multiple
  have hw_add : ∀ U V : W12 Ω, (w (U + V)).1 =ᵐ[volume.restrict Ω] (w U + w V).1 ∧
      ∀ k, (w (U + V)).2 k =ᵐ[volume.restrict Ω] (w U + w V).2 k := by
    intro U V
    refine ⟨?_, fun k => ?_⟩
    · have : ((U + V : W12 Ω) : H1amb Ω) 0 = (U : H1amb Ω) 0 + (V : H1amb Ω) 0 := by
        rw [Submodule.coe_add, PiLp.add_apply]
      simp only [w, this, Prod.fst_add]
      exact Lp.coeFn_add _ _
    · have : ((U + V : W12 Ω) : H1amb Ω) k.succ
          = (U : H1amb Ω) k.succ + (V : H1amb Ω) k.succ := by
        rw [Submodule.coe_add, PiLp.add_apply]
      simp only [w, this, Prod.snd_add, Pi.add_apply]
      exact Lp.coeFn_add _ _
  have hw_smul : ∀ (a : ℝ) (U : W12 Ω), (w (a • U)).1 =ᵐ[volume.restrict Ω] (a • w U).1 ∧
      ∀ k, (w (a • U)).2 k =ᵐ[volume.restrict Ω] (a • w U).2 k := by
    intro a U
    refine ⟨?_, fun k => ?_⟩
    · have : ((a • U : W12 Ω) : H1amb Ω) 0 = a • (U : H1amb Ω) 0 := by
        rw [Submodule.coe_smul, PiLp.smul_apply]
      simp only [w, this, Prod.smul_fst]
      exact Lp.coeFn_smul _ _
    · have : ((a • U : W12 Ω) : H1amb Ω) k.succ = a • (U : H1amb Ω) k.succ := by
        rw [Submodule.coe_smul, PiLp.smul_apply]
      simp only [w, this, Prod.smul_snd, Pi.smul_apply]
      exact Lp.coeFn_smul _ _
  have hsum_pair : ∀ U V : W12 Ω, IntegrableOn (w U + w V).1 Ω volume ∧
      (∀ k, IntegrableOn ((w U + w V).2 k) Ω volume) ∧
      HasWeakGradOn Ω (w U + w V).1 (w U + w V).2 := fun U V =>
    ⟨(hwi U).add (hwi V), fun k => (hwgi U k).add (hwgi V k),
      (hwg U).add (hwi U) (hwi V) (hwgi U) (hwgi V) (hwg V)⟩
  -- linearity of the classes
  let E₀ : W12 Ω →ₗ[ℝ] H1amb (Set.univ : Set (EuclideanSpace ℝ (Fin d))) :=
    { toFun := Eg
      map_add' := by
        intro U V
        obtain ⟨hs1, hs2, hs3⟩ := hsum_pair U V
        obtain ⟨h1, h2⟩ := hcongr (w (U + V)) (w U + w V) (hwi _) (hwgi _) (hwg _) hs1 hs2 hs3
          (hw_add U V).1 (hw_add U V).2
        refine PiLp.ext fun i => ?_
        refine Fin.cases ?_ (fun k => ?_) i
        · rw [PiLp.add_apply, hEg0, hEg0, hEg0]
          apply Lp.ext
          filter_upwards [(hMF' (U + V)).coeFn_toLp,
            Lp.coeFn_add ((hMF' U).toLp _) ((hMF' V).toLp _), (hMF' U).coeFn_toLp,
            (hMF' V).coeFn_toLp, ae_restrict_of_ae h1] with x hx1 hx2 hx3 hx4 hx5
          rw [hx1, hx2, Pi.add_apply, hx3, hx4, hx5, map_add]
          rfl
        · rw [PiLp.add_apply, hEgk, hEgk, hEgk]
          apply Lp.ext
          filter_upwards [(hMG' (U + V) k).coeFn_toLp,
            Lp.coeFn_add ((hMG' U k).toLp _) ((hMG' V k).toLp _), (hMG' U k).coeFn_toLp,
            (hMG' V k).coeFn_toLp, ae_restrict_of_ae (h2 k)] with x hx1 hx2 hx3 hx4 hx5
          rw [hx1, hx2, Pi.add_apply, hx3, hx4, hx5, map_add]
          rfl
      map_smul' := by
        intro a U
        have hs1 : IntegrableOn (a • w U).1 Ω volume := (hwi U).smul a
        have hs2 : ∀ k, IntegrableOn ((a • w U).2 k) Ω volume := fun k => (hwgi U k).smul a
        have hs3 : HasWeakGradOn Ω (a • w U).1 (a • w U).2 := by
          intro φ hφc hφcs hφB k
          have := hwg U φ hφc hφcs hφB k
          simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_assoc,
            integral_const_mul, this, mul_neg]
        obtain ⟨h1, h2⟩ := hcongr (w (a • U)) (a • w U) (hwi _) (hwgi _) (hwg _) hs1 hs2 hs3
          (hw_smul a U).1 (hw_smul a U).2
        refine PiLp.ext fun i => ?_
        refine Fin.cases ?_ (fun k => ?_) i
        · rw [RingHom.id_apply, PiLp.smul_apply, hEg0, hEg0]
          apply Lp.ext
          filter_upwards [(hMF' (a • U)).coeFn_toLp, Lp.coeFn_smul a ((hMF' U).toLp _),
            (hMF' U).coeFn_toLp, ae_restrict_of_ae h1] with x hx1 hx2 hx3 hx4
          rw [hx1, hx2, Pi.smul_apply, hx3, hx4, map_smul]
          rfl
        · rw [RingHom.id_apply, PiLp.smul_apply, hEgk, hEgk]
          apply Lp.ext
          filter_upwards [(hMG' (a • U) k).coeFn_toLp, Lp.coeFn_smul a ((hMG' U k).toLp _),
            (hMG' U k).coeFn_toLp, ae_restrict_of_ae (h2 k)] with x hx1 hx2 hx3 hx4
          rw [hx1, hx2, Pi.smul_apply, hx3, hx4, map_smul]
          rfl }
  -- the bound
  have hFb : ∀ U : W12 Ω, ‖(hMF' U).toLp (T (w U)).1‖ ≤ K * ((d + 1) * ‖U‖) := by
    intro U
    rw [Lp.norm_toLp, Measure.restrict_univ]
    have : eLpNorm (T (w U)).1 2 volume ≤ (K : ℝ≥0∞) * ENNReal.ofReal ((d + 1) * ‖U‖) :=
      (hspec U).2.2.2.2.2.2.1.trans (by gcongr; exact hN U)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)] at this
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) this
  have hGb : ∀ U : W12 Ω, ∀ k, ‖(hMG' U k).toLp ((T (w U)).2 k)‖ ≤ K * ((d + 1) * ‖U‖) := by
    intro U k
    rw [Lp.norm_toLp, Measure.restrict_univ]
    have : eLpNorm ((T (w U)).2 k) 2 volume ≤ (K : ℝ≥0∞) * ENNReal.ofReal ((d + 1) * ‖U‖) :=
      ((hspec U).2.2.2.2.2.2.2 k).trans (by gcongr; exact hN U)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)] at this
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) this
  set C : ℝ := Real.sqrt (d + 1) * (K * (d + 1)) with hC
  have hC0 : 0 ≤ C := by positivity
  have hbound : ∀ U : W12 Ω, ‖E₀ U‖ ≤ C * ‖U‖ := by
    intro U
    have hsq : ‖E₀ U‖ ^ 2 ≤ (d + 1) * (K * ((d + 1) * ‖U‖)) ^ 2 := by
      change ‖Eg U‖ ^ 2 ≤ _
      rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, hEg0]
      simp only [hEgk]
      calc ‖(hMF' U).toLp (T (w U)).1‖ ^ 2 + ∑ k : Fin d, ‖(hMG' U k).toLp ((T (w U)).2 k)‖ ^ 2
          ≤ (K * ((d + 1) * ‖U‖)) ^ 2 + ∑ _k : Fin d, (K * ((d + 1) * ‖U‖)) ^ 2 :=
            add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hFb U) 2)
              (Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hGb U k) 2)
        _ = (d + 1) * (K * ((d + 1) * ‖U‖)) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have h2 : (C * ‖U‖) ^ 2 = (d + 1) * (K * ((d + 1) * ‖U‖)) ^ 2 := by
      rw [hC, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
    exact le_of_sq_le_sq (h2 ▸ hsq) (mul_nonneg hC0 (norm_nonneg _))
  let E₁ : W12 Ω →L[ℝ] H1amb (Set.univ : Set (EuclideanSpace ℝ (Fin d))) :=
    E₀.mkContinuous C hbound
  -- the image lies in the graph space of the whole space
  have hmem : ∀ U : W12 Ω, E₁ U ∈ W12 (Set.univ : Set (EuclideanSpace ℝ (Fin d))) := by
    intro U
    have h := mem_W12_of_hasWeakGradOn (hMF' U) (hMG' U) (by
      have := (hspec U).1
      exact this)
    exact h
  refine ⟨E₁.codRestrict _ hmem, C, fun U => ⟨?_, fun k => ?_⟩, fun U => ?_, fun U => ?_⟩
  · -- agreement of the function coordinate on the domain
    change (((hMF' U).toLp (T (w U)).1 : L2D Set.univ) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => ((U : H1amb Ω) 0 : L2D Ω) x
    have h1 : (((hMF' U).toLp (T (w U)).1 : L2D Set.univ) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume] (T (w U)).1 := ae_of_ae_restrict_univ (hMF' U).coeFn_toLp
    have h2 : (T (w U)).1 =ᵐ[volume.restrict Ω] fun x => ((U : H1amb Ω) 0 : L2D Ω) x :=
      (ae_restrict_iff' hΩopen.measurableSet).mpr
        (Eventually.of_forall fun y hy => (hspec U).2.2.2.2.2.1 y hy)
    exact Filter.EventuallyEq.trans (ae_restrict_of_ae h1) h2
  · -- agreement of the gradient coordinates, by uniqueness of the weak gradient
    change (((hMG' U k).toLp ((T (w U)).2 k) : L2D Set.univ) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => ((U : H1amb Ω) k.succ : L2D Ω) x
    have h1 : (((hMG' U k).toLp ((T (w U)).2 k) : L2D Set.univ) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume] (T (w U)).2 k := ae_of_ae_restrict_univ (hMG' U k).coeFn_toLp
    have hue : (w U).1 =ᵐ[volume.restrict Ω] (T (w U)).1 :=
      (ae_restrict_iff' hΩopen.measurableSet).mpr
        (Eventually.of_forall fun y hy => ((hspec U).2.2.2.2.2.1 y hy).symm)
    have hwuG : HasWeakGradOn Ω (w U).1 (T (w U)).2 :=
      ((hspec U).1.mono (subset_univ _)).congr_ae hue.symm fun _ => EventuallyEq.rfl
    have hge : (T (w U)).2 k =ᵐ[volume.restrict Ω] (w U).2 k :=
      hasWeakGradOn_unique_ae hΩopen hΩopen.measurableSet
        (fun k => ((hspec U).2.2.2.2.1 k).integrableOn) (hwgi U) hwuG (hwg U) k
    exact Filter.EventuallyEq.trans (ae_restrict_of_ae h1) hge
  · -- vanishing outside the given open set
    change ∀ᵐ y ∂volume, y ∉ Ω' →
      (((hMF' U).toLp (T (w U)).1 : L2D Set.univ) : EuclideanSpace ℝ (Fin d) → ℝ) y = 0
    have h1 := ae_of_ae_restrict_univ (hMF' U).coeFn_toLp
    filter_upwards [h1] with y hy hyΩ'
    rw [hy]
    exact image_eq_zero_of_notMem_tsupport fun hc => hyΩ' ((hspec U).2.2.1 hc)
  · exact hbound U

end EllipticPdes.Extension
