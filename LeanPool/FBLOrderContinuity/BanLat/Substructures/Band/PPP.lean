/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

/-
Authors: David Muñoz-Lahoz
-/

public import LeanPool.FBLOrderContinuity.BanLat.Sublattice
public import LeanPool.FBLOrderContinuity.BanLat.Substructures.Band.Projection
public import LeanPool.OrderClosures.BanLat.OrderComplete



/-!
# The (principal) projection property

A vector lattice has the **Projection Property** (PP) when every band is a
projection band, and the **Principal Projection Property** (PPP) when every
principal band is a projection band. Clearly PP implies PPP.

The two main sources of these properties come from order completeness: order
complete vector lattices have PP, and σ-order complete vector lattices have
PPP. Under PPP, two positive elements admit a positive disjoint refinement of
their sum with controlled summands. Finally, PP and PPP both imply the
Archimedean property.
-/

@[expose] public section

/-! ### The projection properties -/

section Defs

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- A vector lattice has the **Projection Property** (PP) when every band in
`X` is a projection band. -/
class HasProjectionProperty (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] : Prop where
  exists_projectionBand : ∀ B : Band X, ∃ P : ProjectionBand X,
    (P : Set X) = (B : Set X)

/-- A vector lattice has the **Principal Projection Property** (PPP) when every
principal band in `X` is a projection band. -/
class HasPrincipalProjectionProperty (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] : Prop where
  exists_projectionBand : ∀ a : X, ∃ P : ProjectionBand X,
    (P : Set X) = (Band.generated ({a} : Set X) : Set X)

/-- PP implies PPP. -/
instance (priority := 100) HasPrincipalProjectionProperty.of_hasProjectionProperty
    [HasProjectionProperty X] : HasPrincipalProjectionProperty X where
  exists_projectionBand a :=
    HasProjectionProperty.exists_projectionBand (Band.generated ({a} : Set X))

end Defs

/-! ### Order completeness implies the projection properties -/

section OrderComplete

/-- An order complete vector lattice has the Projection Property. -/
instance (priority := 100) HasProjectionProperty.of_isOrderComplete
    {X : Type*} [AddCommGroup X] [ConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] :
    HasProjectionProperty X := by
  have : IsVLArchimedean X := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  refine ⟨fun B => ?_⟩
  apply (ProjectionBand.projectionBand_iff_isLUB_inter_Icc B).mpr
  intro x hx
  refine ⟨sSup ((B : Set X) ∩ Set.Icc 0 x),
    isLUB_csSup ⟨0, B.toOrderIdeal.toSubmodule.zero_mem, le_refl 0, hx⟩
      ⟨x, fun _ hy => hy.2.2⟩⟩

/-- A σ-order complete vector lattice has the Principal Projection Property. -/
instance (priority := 100)
    HasPrincipalProjectionProperty.of_isSigmaOrderComplete
    {X : Type*} [AddCommGroup X] [SigmaConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] :
    HasPrincipalProjectionProperty X := by
  have : IsVLArchimedean X := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  refine ⟨fun a => ?_⟩
  have hband_eq : (Band.generated ({a} : Set X) : Set X)
      = (Band.generated ({|a|} : Set X) : Set X) := by
    apply le_antisymm <;> apply Band.generated_le <;> rintro y rfl
    · refine (Band.generated _).mem_of_abs_le_abs
        (Band.subset_generated _ rfl) ?_
      rw [abs_abs]
    · exact (Band.generated _).abs_mem (Band.subset_generated _ rfl)
  have habs_nn : (0 : X) ≤ |a| := abs_nonneg a
  have hLUB : ∀ x : X, 0 ≤ x →
      ∃ s, IsLUB (Set.range fun n : ℕ => x ⊓ (n : ℕ) • |a|) s := by
    intro x hx
    have hcount : (Set.range fun n : ℕ => x ⊓ (n : ℕ) • |a|).Countable :=
      Set.countable_range _
    have hne : (Set.range fun n : ℕ => x ⊓ (n : ℕ) • |a|).Nonempty :=
      Set.range_nonempty _
    have hbdd : BddAbove (Set.range fun n : ℕ => x ⊓ (n : ℕ) • |a|) :=
      ⟨x, by rintro _ ⟨n, rfl⟩; exact inf_le_left⟩
    refine ⟨sSup _,
      fun _ hy => SigmaConditionallyCompleteLattice.le_csSup _ _ hcount hbdd hy,
      fun _ hy => SigmaConditionallyCompleteLattice.csSup_le _ _ hcount hne hy⟩
  obtain ⟨P, hP⟩ :=
    (ProjectionBand.principalBand_projectionBand_iff_isLUB_range habs_nn).mpr hLUB
  exact ⟨P, hP.trans hband_eq.symm⟩

end OrderComplete

section Rest

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-! ### Disjoint refinement of finite positive families

Under PPP, any finite family of positive vectors may be replaced by a
pairwise disjoint family of positive vectors, dominated termwise by the
original family, whose sum equals the supremum of the original family. -/

/-- For two positive elements in a vector lattice with PPP, their sum can be
rewritten as a sum of two positive disjoint elements, with the new summands
dominated by `2 • x` and `2 • y` respectively. -/
theorem exists_disjoint_add_eq_add_of_hasPrincipalProjectionProperty
    [HasPrincipalProjectionProperty X] {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ u v : X, IsVLDisjoint u v ∧ 0 ≤ u ∧ 0 ≤ v ∧
      u ≤ (2 : ℕ) • x ∧ v ≤ (2 : ℕ) • y ∧ u + v = x + y := by
  obtain ⟨P, hP⟩ := HasPrincipalProjectionProperty.exists_projectionBand ((x - y)⁺)
  set a := x + y
  set u := P.bandProjection a
  set v := a - u
  have ha : 0 ≤ a := by simp [a, add_nonneg hx hy]
  have hu_mem : u ∈ (P : Set X) := by
    exact P.bandProjection_mem a
  have hv_mem : v ∈ disjointComplement (P : Set X) := by
    simpa [u, v] using P.id_sub_bandProjection_mem a
  have huv : IsVLDisjoint u v :=
    isVLDisjoint_comm.mp (hv_mem _ hu_mem)
  have hu0 : 0 ≤ u := by
    simpa [u] using Positive.zero_le_iff.mp P.bandProjection_nonneg a ha
  have hv0 : 0 ≤ v := by
    have hu_le_a : u ≤ a := by
      simpa [u] using Positive.le_iff.mp P.bandProjection_le_id a ha
    simpa [v] using sub_nonneg.mpr hu_le_a
  have hmono : Monotone P.bandProjection :=
    Positive.monotone_iff.mpr (Positive.zero_le_iff.mp P.bandProjection_nonneg)
  have hgen_sub :
      (Band.generated ({(x - y)⁺} : Set X) : Set X) ⊆
        disjointComplement ({(x - y)⁻} : Set X) := by
    refine Band.generated_le (B := Band.disjointComplement ({(x - y)⁻} : Set X)) ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    change (x - y)⁺ ∈ disjointComplement ({(x - y)⁻} : Set X)
    rw [mem_disjointComplement_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    exact isVLDisjoint_posPart_negPart (x - y)
  have hneg_mem : (x - y)⁻ ∈ disjointComplement (P : Set X) := by
    intro z hz
    have hz_gen : z ∈ (Band.generated ({(x - y)⁺} : Set X) : Set X) := by
      simpa [hP] using hz
    have hz_dc : z ∈ disjointComplement ({(x - y)⁻} : Set X) :=
      hgen_sub hz_gen
    exact isVLDisjoint_comm.mp (hz_dc _ (Set.mem_singleton _))
  have hPneg_zero : P.bandProjection ((x - y)⁻) = 0 :=
    P.bandProjection_eq_zero_of_mem_dc hneg_mem
  have ha_le_x : a ≤ (2 : ℕ) • x + (x - y)⁻ := by
    have hyx_le : y - x ≤ (x - y)⁻ := by
      rw [show y - x = -(x - y) by abel, negPart_def]
      exact le_sup_left
    calc
      a = (2 : ℕ) • x + (y - x) := by
        simp [a]
        abel
      _ ≤ (2 : ℕ) • x + (x - y)⁻ := by gcongr
  have hu_le : u ≤ (2 : ℕ) • x := by
    calc
      u ≤ P.bandProjection ((2 : ℕ) • x + (x - y)⁻) := by
        simpa [u] using hmono ha_le_x
      _ = P.bandProjection ((2 : ℕ) • x) + P.bandProjection ((x - y)⁻) := by
        rw [map_add]
      _ = P.bandProjection ((2 : ℕ) • x) := by rw [hPneg_zero, add_zero]
      _ ≤ (2 : ℕ) • x := by
        exact Positive.le_iff.mp P.bandProjection_le_id _ (nsmul_nonneg hx 2)
  have hpos_mem : (x - y)⁺ ∈ (P : Set X) := by
    rw [hP]
    exact Band.subset_generated _ rfl
  have hpos_mem_comp :
      (x - y)⁺ ∈ disjointComplement ((Pᶜ : ProjectionBand X) : Set X) := by
    intro z hz
    exact isVLDisjoint_comm.mp (hz _ hpos_mem)
  have hPcpos_zero : (Pᶜ : ProjectionBand X).bandProjection ((x - y)⁺) = 0 :=
    (Pᶜ : ProjectionBand X).bandProjection_eq_zero_of_mem_dc hpos_mem_comp
  have hmono_comp : Monotone (Pᶜ : ProjectionBand X).bandProjection :=
    Positive.monotone_iff.mpr
      (Positive.zero_le_iff.mp (Pᶜ : ProjectionBand X).bandProjection_nonneg)
  have ha_le_y : a ≤ (2 : ℕ) • y + (x - y)⁺ := by
    have hxy_le : x - y ≤ (x - y)⁺ := by
      rw [posPart_def]
      exact le_sup_left
    calc
      a = (2 : ℕ) • y + (x - y) := by
        simp [a]
        abel
      _ ≤ (2 : ℕ) • y + (x - y)⁺ := by gcongr
  have hv_eq : (Pᶜ : ProjectionBand X).bandProjection a = v := by
    rw [ProjectionBand.bandProjection_compl]
    simp [u, v]
  have hv_le : v ≤ (2 : ℕ) • y := by
    calc
      v = (Pᶜ : ProjectionBand X).bandProjection a := hv_eq.symm
      _ ≤ (Pᶜ : ProjectionBand X).bandProjection ((2 : ℕ) • y + (x - y)⁺) :=
        hmono_comp ha_le_y
      _ = (Pᶜ : ProjectionBand X).bandProjection ((2 : ℕ) • y) +
          (Pᶜ : ProjectionBand X).bandProjection ((x - y)⁺) := by
            rw [map_add]
      _ = (Pᶜ : ProjectionBand X).bandProjection ((2 : ℕ) • y) := by
        rw [hPcpos_zero, add_zero]
      _ ≤ (2 : ℕ) • y := by
        exact Positive.le_iff.mp (Pᶜ : ProjectionBand X).bandProjection_le_id _
          (nsmul_nonneg hy 2)
  refine ⟨u, v, huv, hu0, hv0, hu_le, hv_le, ?_⟩
  calc
    u + v = a := by
      simp [v]
    _ = x + y := by simp [a]

/-! ### The Archimedean property -/

private def IsPosSupFromIdeal (J : OrderIdeal X) (x : X) : Prop :=
  ∃ S : Set X, S.Nonempty ∧ S ⊆ (J : Set X) ∧ (∀ s ∈ S, 0 ≤ s) ∧ IsLUB S x

private lemma IsPosSupFromIdeal.zero (J : OrderIdeal X) :
    IsPosSupFromIdeal J (0 : X) :=
  ⟨{0}, Set.singleton_nonempty 0, by rintro _ rfl; exact J.toSubmodule.zero_mem,
    by rintro _ rfl; rfl,
    isLUB_singleton⟩

private lemma IsPosSupFromIdeal.of_mem {J : OrderIdeal X} {x : X}
    (hx0 : 0 ≤ x) (hxJ : x ∈ J) : IsPosSupFromIdeal J x :=
  ⟨{x}, Set.singleton_nonempty x, by rintro _ rfl; exact hxJ, by rintro _ rfl; exact hx0,
    isLUB_singleton⟩

private lemma IsPosSupFromIdeal.mono {J : OrderIdeal X} {x y : X}
    (hx : IsPosSupFromIdeal J x) (hy0 : 0 ≤ y) (hyx : y ≤ x) :
    IsPosSupFromIdeal J y := by
  obtain ⟨S, hSne, hSJ, hS0, hSx⟩ := hx
  refine ⟨(fun s => y ⊓ s) '' S, hSne.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact J.solid (hSJ hs) (le_inf hy0 (hS0 s hs)) inf_le_right
  · rintro _ ⟨s, hs, rfl⟩
    exact le_inf hy0 (hS0 s hs)
  · simpa [inf_eq_left.mpr hyx] using isLUB_inf_const y hSx

private lemma IsPosSupFromIdeal.add {J : OrderIdeal X} {x y : X}
    (hx : IsPosSupFromIdeal J x) (hy : IsPosSupFromIdeal J y) :
    IsPosSupFromIdeal J (x + y) := by
  obtain ⟨S, hSne, hSJ, hS0, hSx⟩ := hx
  obtain ⟨T, hTne, hTJ, hT0, hTy⟩ := hy
  have hLUB : IsLUB ((fun p : X × X => p.1 + p.2) '' (S ×ˢ T)) (x + y) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
      exact add_le_add (hSx.1 hs) (hTy.1 ht)
    · intro u hu
      have hy_le_sub : ∀ s ∈ S, y ≤ u - s := by
        intro s hs
        apply hTy.2
        intro t ht
        exact le_sub_iff_add_le.mpr (by
          rw [add_comm]
          exact hu ⟨(s, t), ⟨hs, ht⟩, rfl⟩)
      exact le_sub_iff_add_le.mp <| hSx.2 fun s hs =>
        le_sub_iff_add_le.mpr <| by
          rw [add_comm]
          exact le_sub_iff_add_le.mp (hy_le_sub s hs)
  refine ⟨(fun p : X × X => p.1 + p.2) '' (S ×ˢ T), hSne.prod hTne |>.image _, ?_, ?_,
    hLUB⟩
  · rintro _ ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
    exact J.toSubmodule.add_mem (hSJ hs) (hTJ ht)
  · rintro _ ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
    exact add_nonneg (hS0 s hs) (hT0 t ht)

private lemma IsPosSupFromIdeal.smul_nonneg {J : OrderIdeal X} {x : X} {c : ℝ}
    (hc : 0 ≤ c) (hx : IsPosSupFromIdeal J x) :
    IsPosSupFromIdeal J (c • x) := by
  obtain ⟨S, hSne, hSJ, hS0, hSx⟩ := hx
  refine ⟨(fun s => c • s) '' S, hSne.image _, ?_, ?_, isLUB_smul_of_nonneg hc hSx⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact J.toSubmodule.smul_mem c (hSJ hs)
  · rintro _ ⟨s, hs, rfl⟩
    exact _root_.smul_nonneg hc (hS0 s hs)

private lemma IsPosSupFromIdeal.sSup {J : OrderIdeal X} {S : Set X} {x : X}
    (hSne : S.Nonempty) (hS : ∀ s ∈ S, IsPosSupFromIdeal J s) (hSx : IsLUB S x) :
    IsPosSupFromIdeal J x := by
  classical
  refine ⟨{a | ∃ s, ∃ hs : s ∈ S, a ∈ (hS s hs).choose}, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := hSne
    exact ⟨(hS s hs).choose_spec.1.choose, s, hs, (hS s hs).choose_spec.1.choose_spec⟩
  · rintro a ⟨s, hs, ha⟩
    exact (hS s hs).choose_spec.2.1 ha
  · rintro a ⟨s, hs, ha⟩
    exact (hS s hs).choose_spec.2.2.1 a ha
  · refine ⟨?_, ?_⟩
    · rintro a ⟨s, hs, ha⟩
      exact (((hS s hs).choose_spec.2.2.2).1 ha).trans (hSx.1 hs)
    · intro u hu
      apply hSx.2
      intro s hs
      exact ((hS s hs).choose_spec.2.2.2).2 (fun a ha => hu ⟨s, hs, ha⟩)

private lemma isPosSupFromIdeal_of_mem_bandGenerated
    (J : OrderIdeal X) {x : X} (hx0 : 0 ≤ x)
    (hxG : x ∈ Band.generated (J : Set X)) :
    IsPosSupFromIdeal J x := by
  let M : Submodule ℝ X :=
    { carrier := {z : X | IsPosSupFromIdeal J |z|}
      add_mem' := fun {a b} ha hb =>
        IsPosSupFromIdeal.mono (IsPosSupFromIdeal.add ha hb) (abs_nonneg _)
          (abs_add_le a b)
      zero_mem' := by simpa using IsPosSupFromIdeal.zero J
      smul_mem' := fun c a ha => by
        change IsPosSupFromIdeal J |c • a|
        rw [abs_smul']
        exact IsPosSupFromIdeal.smul_nonneg (abs_nonneg c) ha }
  let K : OrderIdeal X := OrderIdeal.ofSolid M fun _ b ha hba =>
    IsPosSupFromIdeal.mono ha (abs_nonneg b) hba
  let B : Band X := Band.ofPosDirectedSSupMem K (by
    intro S hSK hS0 _ hSne y hSy
    change IsPosSupFromIdeal J |y|
    have hy0 : 0 ≤ y := by
      obtain ⟨s, hs⟩ := hSne
      exact (hS0 s hs).trans (hSy.1 hs)
    rw [abs_of_nonneg hy0]
    refine IsPosSupFromIdeal.sSup (J := J) hSne ?_ hSy
    intro s hs
    have hsK : s ∈ K := hSK hs
    change IsPosSupFromIdeal J |s| at hsK
    simpa [abs_of_nonneg (hS0 s hs)] using hsK)
  have hle : Band.generated (J : Set X) ≤ B := Band.generated_le (B := B) fun z hz => by
    change IsPosSupFromIdeal J |z|
    exact IsPosSupFromIdeal.of_mem (abs_nonneg z) (J.abs_mem hz)
  have hxB : x ∈ B := hle hxG
  change IsPosSupFromIdeal J |x| at hxB
  simpa [abs_of_nonneg hx0] using hxB

/-- A vector lattice with the Principal Projection Property is Archimedean. -/
theorem isVLArchimedean_of_hasPrincipalProjectionProperty
    [HasPrincipalProjectionProperty X] : IsVLArchimedean X := by
  apply isVLArchimedean_of_eq_zero_of_nonneg_of_forall_nsmul_le
  intro x y hx hxy
  obtain ⟨P, hP⟩ := HasPrincipalProjectionProperty.exists_projectionBand x
  have hy0 : 0 ≤ y := by simpa using hxy 0
  have hxP : x ∈ (P : Set X) := by
    rw [hP]
    exact Band.subset_generated _ rfl
  have hPx : P.bandProjection x = x :=
    P.bandProjection_eq_of_mem hxP
  have hmono : Monotone P.bandProjection :=
    Positive.monotone_iff.mpr (Positive.zero_le_iff.mp P.bandProjection_nonneg)
  have hbound : ∀ n : ℕ, n • x ≤ P.bandProjection y := by
    intro n
    calc
      n • x = P.bandProjection (n • x) := by
        rw [map_nsmul, hPx]
      _ ≤ P.bandProjection y := hmono (hxy n)
  have hPy0 : 0 ≤ P.bandProjection y :=
    Positive.zero_le_iff.mp P.bandProjection_nonneg y hy0
  let J : OrderIdeal X := OrderIdeal.principal x
  have hPy_mem_generated_principal :
      P.bandProjection y ∈ Band.generated (J : Set X) := by
    have hsub : Band.generated ({x} : Set X) ≤ Band.generated (J : Set X) :=
      Band.generated_le (B := Band.generated (J : Set X)) (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact Band.subset_generated _ (show x ∈ (J : Set X) from
          OrderIdeal.self_mem_principal x))
    have hPy_gen_x : P.bandProjection y ∈ Band.generated ({x} : Set X) := by
      change P.bandProjection y ∈ ((Band.generated ({x} : Set X)) : Set X)
      rw [← hP]
      exact P.bandProjection_mem y
    exact hsub hPy_gen_x
  obtain ⟨S, _hSne, hSJ, _hS0, hLUB⟩ :=
    isPosSupFromIdeal_of_mem_bandGenerated J hPy0 hPy_mem_generated_principal
  have hupper : P.bandProjection y - x ∈ upperBounds S := by
    intro s hs
    have hsJ : s ∈ OrderIdeal.principal x := hSJ hs
    obtain ⟨c, hc, hs_abs_le⟩ := OrderIdeal.mem_principal.mp hsJ
    have hs_le_cx : s ≤ c • x := by
      calc
        s ≤ |s| := le_abs_self s
        _ ≤ c • |x| := hs_abs_le
        _ = c • x := by rw [abs_of_nonneg hx]
    obtain ⟨n, hn⟩ := exists_nat_gt (c + 1)
    refine le_sub_iff_add_le.mpr ?_
    calc
      s + x ≤ c • x + x := by simpa [add_comm] using add_le_add_right hs_le_cx x
      _ = (c + 1) • x := by rw [add_smul, one_smul]
      _ ≤ (n : ℝ) • x := smul_le_smul_of_nonneg_right (le_of_lt hn) hx
      _ = n • x := Nat.cast_smul_eq_nsmul ℝ n x
      _ ≤ P.bandProjection y := hbound n
  have hPy_le : P.bandProjection y ≤ P.bandProjection y - x := hLUB.2 hupper
  have hx_nonpos : x ≤ 0 := by
    have hle : P.bandProjection y + x ≤ P.bandProjection y := le_sub_iff_add_le.mp hPy_le
    have hle' : P.bandProjection y + x ≤ P.bandProjection y + 0 := by simpa using hle
    simpa using (add_le_add_iff_left (P.bandProjection y)).mp hle'
  exact le_antisymm hx_nonpos hx

/-- A vector lattice with the Projection Property is Archimedean. -/
theorem isVLArchimedean_of_hasProjectionProperty
    [HasProjectionProperty X] : IsVLArchimedean X :=
  isVLArchimedean_of_hasPrincipalProjectionProperty

end Rest
