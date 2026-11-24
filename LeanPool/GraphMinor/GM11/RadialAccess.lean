/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RadialBasics

/-!
# Reaching a vertex from a region

Let `x` be a vertex of a drawing `Γ` with at least one half-edge, and let `p` be a region with `x`
in
its closure. This file builds a path from `x` that stays in `p` after time `0`.

* With two or more half-edges at `x`, the path runs inside the closed disc `Q k` of a sector
  (`exists_path_into_disc`).
* With one half-edge, `x` is a leaf, and the sector is missing. Then the path is an infinite
  concatenation of ever shorter paths, whose existence comes from `exists_leaf_nbhd`
  (`exists_path_of_steps`).
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface Filter unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A closed surface is locally path connected. -/
theorem IsClosedSurface.locPathConnected (hS : IsClosedSurface S) : LocallyPathConnectedSpace S
  := by
  have hP : LocallyPathConnectedSpace OpenUnitDisc :=
    (Metric.isOpen_ball : IsOpen (Metric.ball (0 : EuclideanPlane) 1)).locallyPathConnectedSpace
  refine ⟨fun x => ⟨fun U => ⟨fun hU => ?_, fun h => ?_⟩⟩⟩
  swap
  · obtain ⟨s, ⟨hs, -⟩, hsub⟩ := h
    exact mem_of_superset hs hsub
  obtain ⟨V, hV, hxV, ⟨h⟩⟩ := hS.2.2 x
  let T : OpenUnitDisc → S := fun y => (h.symm y).1
  have hTe : IsOpenEmbedding T := hV.isOpenEmbedding_subtypeVal.comp h.symm.isOpenEmbedding
  let c : OpenUnitDisc := h ⟨x, hxV⟩
  have hTc : T c = x := by simp [T, c]
  have hU' : T ⁻¹' U ∈ 𝓝 c := (hTe.continuous.tendsto c).mono_right (by rw [hTc]) hU
  obtain ⟨s, ⟨hs, hsp⟩, hsub⟩ := (path_connected_basis c).mem_iff.mp hU'
  refine ⟨T '' s, ⟨?_, hsp.image hTe.continuous⟩, image_subset_iff.mpr hsub⟩
  rw [← hTc, ← hTe.map_nhds_eq]
  exact image_mem_map hs

/-- An open connected subset of a closed surface is path connected. -/
theorem isPathConnected_of_isOpen (hS : IsClosedSurface S) {A : Set S} (hA : IsOpen A)
    (hc : IsPreconnected A) (hne : A.Nonempty) : IsPathConnected A := by
  have := IsClosedSurface.locPathConnected hS
  exact hA.isConnected_iff_isPathConnected.mp ⟨hne, hc⟩

/-- The concatenation of infinitely many paths `p n` from `y n` to `y (n + 1)`, which tend to `x`.
It
runs from `x` at time `0`, through all the paths in the reverse order, to `y 0` at time `1`. -/
theorem exists_path_of_steps {x : S} {y : ℕ → S} (p : ∀ n, Path (y n) (y (n + 1)))
    {N : ℕ → Set S} (hN : ∀ O ∈ 𝓝 x, ∃ n₀, ∀ n ≥ n₀, N n ⊆ O) (hpN : ∀ n t, p n t ∈ N n) :
    ∃ g : I → S, Continuous g ∧ g 0 = x ∧ ∀ t, 0 < t → ∃ n s, g t = p n s := by
  classical
  let cl : ℝ → I := projIcc 0 1 zero_le_one
  have hcl : Continuous cl := continuous_projIcc
  let F : ℝ → S := fun u => p ⌊u⌋₊ (cl (u - ⌊u⌋₊))
  let C : ℕ → Set ℝ := fun n => if n = 0 then Iic 1 else Icc (n : ℝ) (n + 1)
  have hfl : ∀ (u : ℝ) (m : ℕ), ⌊u⌋₊ = m → F u = p m (cl (u - m)) := by
    rintro u m rfl
    rfl
  have hFeq : ∀ (n : ℕ) (u : ℝ), u ∈ C n → F u = p n (cl (u - n)) := by
    have key : ∀ (n : ℕ) (u : ℝ), u ∈ Icc (n : ℝ) (n + 1) → F u = p n (cl (u - n)) := by
      intro n u hu
      rcases eq_or_lt_of_le hu.2 with h | h
      · have hf : ⌊u⌋₊ = n + 1 := by
          rw [h]
          exact_mod_cast Nat.floor_natCast (R := ℝ) (n + 1)
        rw [hfl u _ hf]
        have e₁ : cl (u - (n + 1 : ℕ)) = 0 := by
          rw [h]
          have : ((n : ℝ) + 1 - (n + 1 : ℕ)) = 0 := by push_cast; ring
          rw [this]
          exact projIcc_left _
        have e₂ : cl (u - n) = 1 := by
          rw [h]
          have : ((n : ℝ) + 1 - n) = 1 := by ring
          rw [this]
          exact projIcc_right _
        rw [e₁, e₂, (p (n + 1)).source, (p n).target]
      · exact hfl u n ((Nat.floor_eq_iff (le_trans (Nat.cast_nonneg n) hu.1)).mpr ⟨hu.1, h⟩)
    intro n u hu
    by_cases hn : n = 0
    · subst hn
      have hu1 : u ≤ 1 := by simpa [C] using hu
      rcases le_or_gt 0 u with h0 | h0
      · exact key 0 u (by simpa using ⟨h0, hu1⟩)
      · exact hfl u 0 (Nat.floor_of_nonpos h0.le)
    · have : u ∈ Icc (n : ℝ) (n + 1) := by simpa [C, hn] using hu
      exact key n u this
  have hFc : Continuous F := by
    have hlf : LocallyFinite C := by
      intro u
      refine ⟨Ioo (u - 1) (u + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
      refine (finite_Iic ⌈u + 1⌉₊).subset ?_
      rintro n ⟨z, hz, hzI⟩
      by_cases hn : n = 0
      · subst hn
        exact Nat.zero_le _
      · have hz' : z ∈ Icc (n : ℝ) (n + 1) := by simpa [C, hn] using hz
        have : (n : ℝ) ≤ ⌈u + 1⌉₊ := calc
          (n : ℝ) ≤ z := hz'.1
          _ ≤ u + 1 := hzI.2.le
          _ ≤ _ := Nat.le_ceil _
        exact_mod_cast this
    refine hlf.continuous ?_ ?_ ?_
    · refine eq_univ_of_forall fun u => mem_iUnion.mpr ?_
      rcases le_or_gt u 1 with h | h
      · exact ⟨0, by simpa [C] using h⟩
      · have hf : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by simpa using h.le)
        refine ⟨⌊u⌋₊, ?_⟩
        have hn : ⌊u⌋₊ ≠ 0 := by omega
        simp only [C, hn, ite_false]
        exact ⟨Nat.floor_le (by linarith), (Nat.lt_floor_add_one u).le⟩
    · intro n
      by_cases hn : n = 0 <;> simp [C, hn, isClosed_Iic, isClosed_Icc]
    · intro n
      have hc : Continuous fun u : ℝ => p n (cl (u - n)) :=
        (p n).continuous.comp (hcl.comp (by fun_prop))
      exact hc.continuousOn.congr (hFeq n)
  let g : I → S := fun t => if (t : ℝ) = 0 then x else F ((t : ℝ)⁻¹ - 1)
  have hg0 : g 0 = x := by simp [g]
  have hgF : ∀ t : I, (t : ℝ) ≠ 0 → g t = F ((t : ℝ)⁻¹ - 1) := fun t ht => ite_eq_right ht
  refine ⟨g, ?_, hg0, ?_⟩
  · refine continuous_iff_continuousAt.mpr fun t => ?_
    by_cases ht : (t : ℝ) = 0
    · have ht0 : t = 0 := Subtype.ext ht
      subst ht0
      change Tendsto g (𝓝 0) (𝓝 (g 0))
      rw [hg0]
      refine fun O hO => ?_
      obtain ⟨n₀, hn₀⟩ := hN O hO
      have hpos : (0 : ℝ) < ((n₀ : ℝ) + 1)⁻¹ := by positivity
      have : ∀ᶠ t : I in 𝓝 0, (t : ℝ) < ((n₀ : ℝ) + 1)⁻¹ :=
        continuous_subtype_val.continuousAt.eventually_lt_const (by simpa using hpos)
      refine mem_map.mpr ?_
      filter_upwards [this] with t ht
      by_cases ht0 : (t : ℝ) = 0
      · have e : g t = x := ite_eq_left ht0
        rw [mem_preimage, e]
        exact mem_of_mem_nhds hO
      · have htp : (0 : ℝ) < t := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
        rw [mem_preimage, hgF t ht0]
        have hu : (n₀ : ℝ) ≤ (t : ℝ)⁻¹ - 1 := by
          have := (inv_lt_inv₀ (by positivity) htp).mpr ht
          rw [inv_inv] at this
          linarith
        exact hn₀ ⌊(t : ℝ)⁻¹ - 1⌋₊ (Nat.le_floor hu) (hpN _ _)
    · have hev : g =ᶠ[𝓝 t] fun t' : I => F ((t' : ℝ)⁻¹ - 1) := by
        have : ∀ᶠ t' : I in 𝓝 t, (t' : ℝ) ≠ 0 :=
          continuous_subtype_val.continuousAt.eventually_ne ht
        filter_upwards [this] with t' ht' using hgF t' ht'
      refine ContinuousAt.congr ?_ hev.symm
      refine hFc.continuousAt.comp ?_
      exact (ContinuousAt.inv₀ continuous_subtype_val.continuousAt ht).sub continuousAt_const
  · intro t ht
    have ht' : (t : ℝ) ≠ 0 := fun h => ht.ne' (Subtype.ext h)
    exact ⟨_, _, hgF t ht'⟩

/-- A path from a point of the boundary of a closed disc into the interior of the disc, near that
point. -/
theorem exists_path_into_disc {Q : Set S} (hQ : IsClosedDisc Q) {x : S} (hx : x ∈ discBd Q)
    {W : Set S} (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ g : I → S, Continuous g ∧ Function.Injective g ∧ g 0 = x ∧
      ∀ t, 0 < t → g t ∈ W ∧ g t ∈ Q ∧ g t ∉ discBd Q := by
  obtain ⟨φ⟩ := hQ
  have hbd := disc_boundary Q φ
  rw [hbd] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  have hbn : ‖(b : EuclideanPlane)‖ = 1 := by simpa [UnitCircle] using hb
  -- The points of the radius ending at `b`.
  let pt : I → ClosedUnitDisc := fun s => ⟨(1 - (s : ℝ)) • (b : EuclideanPlane), by
    have : ‖(1 - (s : ℝ)) • (b : EuclideanPlane)‖ ≤ 1 := by
      rw [norm_smul, hbn, mul_one, Real.norm_of_nonneg (by linarith [s.2.2])]
      linarith [s.2.1]
    simpa [ClosedUnitDisc] using this⟩
  have hpt : Continuous pt := Continuous.subtype_mk (by fun_prop) _
  have hpt0 : pt 0 = b := Subtype.ext (by simp [pt])
  let m : I → S := fun s => (φ (pt s)).1
  have hm : Continuous m := continuous_subtype_val.comp (φ.continuous.comp hpt)
  have hmW : IsOpen (m ⁻¹' W) := hW.preimage hm
  have h0W : (0 : I) ∈ m ⁻¹' W := by
    change (φ (pt 0)).1 ∈ W
    rw [hpt0]
    exact hxW
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hmW 0 h0W
  let d : ℝ := min (δ / 2) 1
  have hd0 : 0 < d := lt_min (half_pos hδ) one_pos
  have hd1 : d ≤ 1 := min_le_right _ _
  let sc : I → I := fun t => ⟨d * t, mul_nonneg hd0.le t.2.1, by nlinarith [t.2.1, t.2.2]⟩
  have hsc : Continuous sc := Continuous.subtype_mk (by fun_prop) _
  refine ⟨m ∘ sc, hm.comp hsc, ?_, ?_, ?_⟩
  · intro s t h
    have h₁ : pt (sc s) = pt (sc t) := φ.injective (Subtype.ext h)
    have h₂ := congrArg Subtype.val h₁
    have hne : (b : EuclideanPlane) ≠ 0 := fun h0 => by simp [h0] at hbn
    have h₃ := smul_left_injective ℝ hne h₂
    exact Subtype.ext (mul_left_cancel₀ hd0.ne' (by linarith [h₃, show (sc s : ℝ) = d * s from rfl,
      show (sc t : ℝ) = d * t from rfl]))
  · change (φ (pt (sc 0))).1 = _
    have : sc 0 = 0 := Subtype.ext (by simp [sc])
    rw [this, hpt0]
  · intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hs : (sc t : ℝ) = d * t := rfl
    have hs0 : 0 < (sc t : ℝ) := by rw [hs]; positivity
    refine ⟨hball ?_, (φ _).2, ?_⟩
    · rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
      have : (sc t : ℝ) ≤ δ / 2 := by
        rw [hs]
        have h₁ : d ≤ δ / 2 := min_le_left _ _
        nlinarith [t.2.1, t.2.2]
      change |(sc t : ℝ) - ((0 : I) : ℝ)| < δ
      rw [Icc.coe_zero, sub_zero, abs_of_pos hs0]
      linarith
    · rw [hbd]
      rintro ⟨z, hz, hze⟩
      have hzp : z = pt (sc t) := φ.injective (Subtype.ext hze)
      have hzn : ‖(z : EuclideanPlane)‖ = 1 := by simpa [UnitCircle] using hz
      rw [hzp] at hzn
      have hle : (sc t : ℝ) ≤ 1 := (sc t).2.2
      have : ‖(1 - (sc t : ℝ)) • (b : EuclideanPlane)‖ = 1 - (sc t : ℝ) := by
        rw [norm_smul, hbn, mul_one, Real.norm_of_nonneg (by linarith)]
      have h₂ : ‖(pt (sc t) : EuclideanPlane)‖ = 1 - (sc t : ℝ) := this
      linarith

/-- A path that starts at a leaf and then stays in a region whose closure contains the leaf. -/
theorem exists_path_of_leaf (hS : IsClosedSurface S) (Γ : Drawing S) {e : Set S} (he : e ∈ Γ.E)
    {u v : S} (huv : u ≠ v) (hcap : closure e ∩ Γ.V = {u, v}) (hL : IsLineWithEnds (closure e) u v)
    (hleaf : ∀ f ∈ Γ.E, f ≠ e → v ∉ closure f) {p : Set S} (hp : p ∈ Γ.R)
    (hvp : v ∈ closure p) :
    ∃ g : I → S, Continuous g ∧ g 0 = v ∧ ∀ t, 0 < t → g t ∈ p := by
  classical
  have : T2Space S := hS.2.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hC : (𝓝 v).IsCountablyGenerated := by
    obtain ⟨V₀, hV₀, hvV₀, ⟨h⟩⟩ := hS.2.2 v
    let T : OpenUnitDisc → S := fun y => (h.symm y).1
    have hTe : IsOpenEmbedding T := hV₀.isOpenEmbedding_subtypeVal.comp h.symm.isOpenEmbedding
    have hTc : T (h ⟨v, hvV₀⟩) = v := by simp [T]
    rw [← hTc, ← hTe.map_nhds_eq]
    infer_instance
  obtain ⟨B, hB⟩ := (𝓝 v).exists_antitone_basis
  let Nb := {N : Set S // IsOpen N ∧ v ∈ N}
  have hstep : ∀ N : Nb, ∃ Z : Nb, ∀ x ∈ Z.1, x ∉ Γ.U → ∀ y ∈ Z.1, y ∉ Γ.U →
      ∃ A : Set S, IsPreconnected A ∧ Disjoint A Γ.U ∧ x ∈ A ∧ y ∈ A ∧ A ⊆ N.1 := fun N => by
    obtain ⟨Z, h₁, h₂, h₃⟩ := exists_leaf_nbhd hS Γ he huv hcap hL hleaf N.2.1 N.2.2
    exact ⟨⟨Z, h₁, h₂⟩, h₃⟩
  choose Z hZ using hstep
  let O : ℕ → Nb := fun n => Nat.rec ⟨univ, isOpen_univ, mem_univ _⟩
    (fun n N => ⟨(Z N).1 ∩ interior (B n) ∩ N.1, ((Z N).2.1.inter isOpen_interior).inter N.2.1,
      ⟨(Z N).2.2, mem_interior_iff_mem_nhds.mpr (hB.mem n)⟩, N.2.2⟩) n
  have hOs : ∀ n, (O (n + 1)).1 = (Z (O n)).1 ∩ interior (B n) ∩ (O n).1 := fun _ => rfl
  have hy : ∀ n, ∃ y, y ∈ (O (n + 1)).1 ∧ y ∈ p := fun n =>
    mem_closure_iff.mp hvp _ (O (n + 1)).2.1 (O (n + 1)).2.2
  choose y hyO hyp using hy
  have hyU : ∀ n, y n ∉ Γ.U := fun n => region_subset hp (hyp n)
  have hpath : ∀ n, ∃ P : Path (y n) (y (n + 1)), ∀ t, P t ∈ (O n).1 ∧ P t ∈ p := by
    intro n
    have h₁ : y n ∈ (Z (O n)).1 := by
      exact (show y n ∈ (Z (O n)).1 ∩ interior (B n) ∩ (O n).1 from hyO n).1.1
    have h₂ : y (n + 1) ∈ (Z (O n)).1 := by
      have h₃ : y (n + 1) ∈ (O (n + 1)).1 :=
        (show y (n + 1) ∈ (Z (O (n + 1))).1 ∩ interior (B (n + 1)) ∩ (O (n + 1)).1 from hyO
          (n + 1)).2
      exact (show y (n + 1) ∈ (Z (O n)).1 ∩ interior (B n) ∩ (O n).1 from h₃).1.1
    obtain ⟨A, hA, hAU, hyA, hyA', hAO⟩ := hZ (O n) _ h₁ (hyU n) _ h₂ (hyU (n + 1))
    have hE : IsOpen ((O n).1 \ Γ.U) := (O n).2.1.sdiff Γ.isClosed_U
    let E : Set S := connectedComponentIn ((O n).1 \ Γ.U) (y n)
    have hEo : IsOpen E := hE.connectedComponentIn
    have hEs : E ⊆ (O n).1 \ Γ.U := connectedComponentIn_subset _ _
    have hyAs : A ⊆ (O n).1 \ Γ.U := fun z hz => ⟨hAO hz, disjoint_left.mp hAU hz⟩
    have hyE : y n ∈ E := mem_connectedComponentIn (hyAs hyA)
    have hAE : A ⊆ E := hA.subset_connectedComponentIn hyA hyAs
    have hEp : IsPathConnected E := isPathConnected_of_isOpen hS hEo
      isPreconnected_connectedComponentIn ⟨_, hyE⟩
    have hEd : Disjoint E Γ.U := disjoint_left.mpr fun z hz => (hEs hz).2
    have hEr : E ⊆ p := subset_region hp isPreconnected_connectedComponentIn hEd hyE (hyp n)
    obtain ⟨P, hP⟩ := hEp.joinedIn _ hyE _ (hAE hyA')
    exact ⟨P, fun t => ⟨(hEs (hP t)).1, hEr (hP t)⟩⟩
  choose P hP using hpath
  have hN : ∀ O' ∈ 𝓝 v, ∃ n₀, ∀ n ≥ n₀, (O n).1 ⊆ O' := by
    intro O' hO'
    obtain ⟨m, -, hm⟩ := hB.1.mem_iff.mp hO'
    refine ⟨m + 1, fun n hn => ?_⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact fun z hz => hm (hB.2 (show m ≤ n' by omega) (interior_subset
      (show z ∈ (Z (O n')).1 ∩ interior (B n') ∩ (O n').1 from hz).1.2))
  obtain ⟨g, hg, hg0, hgt⟩ := exists_path_of_steps P hN fun n t => (hP n t).1
  refine ⟨g, hg, hg0, fun t ht => ?_⟩
  obtain ⟨n, s, hs⟩ := hgt t ht
  rw [hs]
  exact (hP n s).2

/-- A path from a vertex with a half-edge into a region whose closure contains the vertex. -/
theorem exists_access (hS : IsClosedSurface S) (Γ : Drawing S) {γ : Set S → I → S}
    (hγ : EdgePar Γ γ) {x : S} (hx : x ∈ Γ.V) (hne : (halfEdges Γ γ x).Nonempty) {p : Set S}
    (hp : p ∈ Γ.R) (hxp : x ∈ closure p) :
    ∃ g : I → S, Continuous g ∧ g 0 = x ∧ ∀ t, 0 < t → g t ∈ p := by
  classical
  have : T2Space S := hS.2.1
  by_cases h2 : 2 ≤ Nat.card (halfEdges Γ γ x)
  · obtain ⟨next, ρ, P, W, Q, τ, h⟩ := exists_sectors hS Γ hγ hx h2
    obtain ⟨k, rfl⟩ := IsCorners.all (IsSectors.corners h) p hp hxp
    obtain ⟨g, hg, -, hg0, hgt⟩ := exists_path_into_disc (IsSectors.disc h k) (IsSectors.bd h k)
      (IsSectors.isOpen h) (IsSectors.mem h)
    refine ⟨g, hg, hg0, fun t ht => IsSectors.sub h k (IsSectors.inside h k ?_)⟩
    obtain ⟨h₁, h₂, h₃⟩ := hgt t ht
    exact ⟨⟨h₁, h₂⟩, h₃⟩
  · have hfin := finite_halfEdges Γ γ x
    have : Fintype (halfEdges Γ γ x) := hfin.fintype
    obtain ⟨⟨e, b⟩, he, hb⟩ := hne
    dsimp only at he hb
    have hsingle : ∀ y ∈ halfEdges Γ γ x, y = (e, b) := by
      intro y hy
      by_contra hne'
      apply h2
      have hc : 1 < (halfEdges Γ γ x).ncard := (one_lt_ncard hfin).mpr
        ⟨y, hy, (e, b), ⟨he, hb⟩, hne'⟩
      exact hc
    have hother : γ e (endOf (!b)) ≠ x := by
      intro h'
      have := hsingle (e, !b) ⟨he, h'⟩
      simp at this
    have hxcl : x ∈ closure e := hb ▸ end_mem_closure hγ he b
    have hoV := end_mem_V hγ he (!b)
    have hocl := end_mem_closure hγ he (!b)
    have hleaf : ∀ f ∈ Γ.E, f ≠ e → x ∉ closure f := by
      intro f hf hfe hxf
      obtain ⟨c, hc⟩ := exists_end_eq hγ hf hx hxf
      have := hsingle (f, c) ⟨hf, hc⟩
      exact hfe (congrArg Prod.fst this)
    rcases Γ.edge_cond e he with ⟨u, v, huv, hcap, hL⟩ | ⟨u, hcap, -⟩
    · have hxm : x ∈ ({u, v} : Set S) := by
        rw [← hcap]
        exact ⟨hxcl, hx⟩
      rcases hxm with rfl | hxv
      · rw [pair_comm] at hcap
        exact exists_path_of_leaf hS Γ he huv.symm hcap (IsLineWithEnds.symm hL) hleaf hp hxp
      · obtain rfl : x = v := hxv
        exact exists_path_of_leaf hS Γ he huv hcap hL hleaf hp hxp
    · have h₁ : x ∈ ({u} : Set S) := by
        rw [← hcap]
        exact ⟨hxcl, hx⟩
      have h₂ : γ e (endOf (!b)) ∈ ({u} : Set S) := by
        rw [← hcap]
        exact ⟨hocl, hoV⟩
      exact absurd (h₂.trans h₁.symm) hother

end GraphMinor.GM11
