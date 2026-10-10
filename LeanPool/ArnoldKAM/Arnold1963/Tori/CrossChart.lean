/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Main.GlobalCover
public import LeanPool.ArnoldKAM.Arnold1963.Tori.OrbitClosure

/-!
Intersecting tori from different charts coincide by uniqueness of the original Hamiltonian
trajectory and density of its orbit. The global family removes duplicate sets, retaining
distinct branches that can have the same frequency.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal
namespace KamProject.Arnold1963.FiniteLocalization
variable {n : ℕ} {H₀ : ComplexSpace n → ℂ} {ambient : Set (ComplexSpace n)}
  {ρ : ℝ≥0} {κ : ℝ} (L : FiniteLocalization n H₀ ambient ρ κ)
  (f : AnalyticPhaseFunction n ambient ρ) (hf : f.uniformNorm ≤ L.threshold)

theorem tori_eq_of_intersection (c d : L.patches) {p p' : RealSpace n}
    (hp : p ∈ realSlice ((L.data f hf c).limitDomain (L.parameters c)))
    (hp' : p' ∈ realSlice ((L.data f hf d).limitDomain (L.parameters d)))
    {z : RealPhaseSpace n}
    (hz : z ∈ (L.data f hf c).invariantTorus (L.parameters c) p)
    (hz' : z ∈ (L.data f hf d).invariantTorus (L.parameters d) p') :
    (L.data f hf c).invariantTorus (L.parameters c) p =
      (L.data f hf d).invariantTorus (L.parameters d) p' := by
  let h := L.data f hf c
  let h' := L.data f hf d
  let b := L.parameters c
  let b' := L.parameters d
  rw [← h.torusEmbedding_range b p] at hz
  rw [← h'.torusEmbedding_range b' p'] at hz'
  obtain ⟨Q, hQ⟩ := hz
  obtain ⟨Q', hQ'⟩ := hz'
  let x := torusRepresentative (p, Q)
  let y := torusRepresentative (p', Q')
  have he : torusProjection (h.realLimitMap b x) = torusProjection (h'.realLimitMap b' y) :=
    hQ.trans hQ'.symm
  obtain ⟨k, hk⟩ := (torusProjection_eq_iff _ _).mp he
  have heR : h.realLimitMap b x = h'.realLimitMap b' (realPhaseShift k y) :=
    hk.trans (h'.realLimitMap_shift b' (x := y) hp' k).symm
  have he0 : h.orbit b p x.2 0 = h'.orbit b' p' (y.2 + realAngleShift k) 0 := by
    rw [h.orbit_initial, h'.orbit_initial]
    have hh := congrArg complexifyPhase heR
    change complexifyPhase (realPartPhase (h.limitMap b (complexifyPhase x))) =
      complexifyPhase (realPartPhase (h'.limitMap b' (complexifyPhase (realPhaseShift k y)))) at hh
    rw [h.limitMap_real_value b hp, h'.limitMap_real_value b' hp'] at hh
    exact hh
  have heo : h.orbit b p x.2 = h'.orbit b' p' (y.2 + realAngleShift k) :=
    eq_of_analytic_autonomous_orbits
      (X := hamiltonianVectorField (fun w => H₀ w.1 + f.toFun w))
      (fun t => h.vectorField_analytic b 0 _ (h.orbit_mem_initial b hp x.2 t))
      (L.orbit_original f hf c hp x.2)
      (L.orbit_original f hf d hp' (y.2 + realAngleShift k)) he0
  rw [← h.projected_orbit_closure b hp x.2,
    ← h'.projected_orbit_closure b' hp' (y.2 + realAngleShift k), heo]

/-- The invariant torus sets realized by all retained labels in the finite patch collection. -/
def tori : Set (Set (RealPhaseSpace n)) :=
  {T | ∃ c : L.patches, ∃ p ∈ realSlice ((L.data f hf c).limitDomain (L.parameters c)),
    T = (L.data f hf c).invariantTorus (L.parameters c) p}

theorem tori_pairwise_disjoint : (L.tori f hf).Pairwise Disjoint := by
  intro T hT U hU hne
  obtain ⟨c, p, hp, rfl⟩ := hT
  obtain ⟨d, p', hp', rfl⟩ := hU
  apply disjoint_left.mpr
  intro z hz hz'
  exact hne (L.tori_eq_of_intersection f hf c d hp hp' hz hz')

theorem goodSet_eq_sUnion_tori : L.goodSet f hf = ⋃₀ L.tori f hf := by
  ext z
  constructor
  · intro hz
    obtain ⟨c, hc⟩ := mem_iUnion.mp hz
    rw [(L.data f hf c).localF1_eq_union (L.parameters c)] at hc
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp hc
    exact mem_sUnion.mpr ⟨_, ⟨c, p, hp, rfl⟩, hzp⟩
  · rintro ⟨T, ⟨c, p, hp, rfl⟩, hz⟩
    apply mem_iUnion.mpr
    refine ⟨c, ?_⟩
    rw [(L.data f hf c).localF1_eq_union (L.parameters c)]
    exact mem_iUnion₂.mpr ⟨p, hp, hz⟩

end KamProject.Arnold1963.FiniteLocalization
