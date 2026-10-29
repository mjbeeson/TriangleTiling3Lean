/-
Restricting a tiling to a sub-triangle.

If `T'` is a triangle inside the tiled triangle whose boundary meets no tile's interior (for
example, its sides lie on sides of the tiled triangle or along tile edges), then the tiles lying
in `T'` tile `T'` exactly. Every tile either lies in `T'` or has interior disjoint from it.

This turns arguments "on one side of an internal segment" into ordinary statements about a
smaller tiling, to which the angle sums (`Dissection.sum_localAngle_eq`) and the side walks
(`Dissection.side_walk`) apply directly.
-/
import Erdos634.AngleSumDissection
import Erdos634.Congruence

namespace TriangleTiling

open Erdos634.Geometry MeasureTheory Set

/-- A triangle is the closure of its interior. -/
theorem tri_closure_interior (T : Tri) : closure (interior T.carrier) = T.carrier := by
  rw [T.convex.closure_interior_eq_closure_of_nonempty_interior T.interior_nonempty,
    T.isCompact.isClosed.closure_eq]

/-- If no tile's interior meets the frontier of `T'`, a tile whose interior meets the interior
of `T'` lies in `T'`. -/
theorem tile_subset_of_interior_meet {N : ℕ} (D : Dissection N) (T' : Tri)
    (hwall : ∀ y ∈ frontier T'.carrier, ∀ i, y ∉ interior (D.tile i).carrier)
    (i : Fin N) (h : (interior (D.tile i).carrier ∩ interior T'.carrier).Nonempty) :
    (D.tile i).carrier ⊆ T'.carrier := by
  obtain ⟨x, hxi, hxT⟩ := h
  intro y hy
  by_contra hyT
  have hopen : IsOpen T'.carrierᶜ := T'.isCompact.isClosed.isOpen_compl
  have hycl : y ∈ closure (interior (D.tile i).carrier) := by
    rw [tri_closure_interior]; exact hy
  -- An interior point `y'` of the tile outside `T'`.
  obtain ⟨y', hy'T, hy'i⟩ := mem_closure_iff.mp hycl _ hopen hyT
  -- The segment from `x` to `y'` lies in the tile's interior, and must cross `frontier T'`.
  have hseg : segment ℝ x y' ⊆ interior (D.tile i).carrier :=
    (D.tile i).convex.interior.segment_subset hxi hy'i
  have hpc : IsPreconnected (segment ℝ x y') := (convex_segment x y').isPreconnected
  obtain ⟨z, -, hz1, hz2⟩ := hpc (interior T'.carrier) T'.carrierᶜ isOpen_interior hopen
    (by
      intro z hz
      by_cases hzi : z ∈ interior T'.carrier
      · exact Or.inl hzi
      · refine Or.inr fun hzT => ?_
        exact hwall z ⟨subset_closure hzT, hzi⟩ i (hseg hz))
    ⟨x, left_mem_segment _ _ _, hxT⟩ ⟨y', right_mem_segment _ _ _, hy'T⟩
  exact hz2 (interior_subset hz1)

open Classical in
/-- The tiles lying in `T'`. -/
noncomputable def insideTiles {N : ℕ} (D : Dissection N) (T' : Tri) : Finset (Fin N) :=
  Finset.univ.filter fun i => (D.tile i).carrier ⊆ T'.carrier

theorem mem_insideTiles {N : ℕ} {D : Dissection N} {T' : Tri} {i : Fin N} :
    i ∈ insideTiles D T' ↔ (D.tile i).carrier ⊆ T'.carrier := by
  classical
  simp [insideTiles]

/-- **The restriction covers.** If `T'` lies in the target and no tile's interior meets its
frontier, the tiles lying in `T'` cover `T'`. -/
theorem insideTiles_cover {N : ℕ} (D : Dissection N) (T' : Tri)
    (hsub : T'.carrier ⊆ D.target.carrier)
    (hwall : ∀ y ∈ frontier T'.carrier, ∀ i, y ∉ interior (D.tile i).carrier) :
    (⋃ i ∈ insideTiles D T', (D.tile i).carrier) = T'.carrier := by
  classical
  apply Subset.antisymm
  · exact iUnion₂_subset fun i hi => mem_insideTiles.mp hi
  intro x hx
  by_contra hxU
  set U := (⋃ i ∈ insideTiles D T', (D.tile i).carrier)ᶜ with hUdef
  have hUopen : IsOpen U :=
    (isClosed_biUnion_finset fun i _ => (D.tile i).isCompact.isClosed).isOpen_compl
  have hx' : x ∈ closure (interior T'.carrier) := by rw [tri_closure_interior]; exact hx
  obtain ⟨w, hwU, hwint⟩ := mem_closure_iff.mp hx' U hUopen hxU
  -- A point of `U ∩ interior T'` on no tile's frontier: the frontiers are null.
  have hVopen : IsOpen (U ∩ interior T'.carrier) := hUopen.inter isOpen_interior
  have hVpos : 0 < volume (U ∩ interior T'.carrier) := hVopen.measure_pos volume ⟨w, hwU, hwint⟩
  have hF : volume (⋃ i, frontier (D.tile i).carrier) = 0 :=
    measure_iUnion_null fun i => (D.tile i).volume_frontier
  have hnot : ¬ (U ∩ interior T'.carrier ⊆ ⋃ i, frontier (D.tile i).carrier) := by
    intro h
    have := measure_mono (μ := volume) h
    rw [hF] at this
    exact absurd (lt_of_lt_of_le hVpos this) (lt_irrefl 0)
  obtain ⟨y, hyV, hyF⟩ := not_subset.mp hnot
  have hyT : y ∈ D.target.carrier := hsub (interior_subset hyV.2)
  rw [← D.covers] at hyT
  obtain ⟨j, hj⟩ := mem_iUnion.mp hyT
  have hyj : y ∈ interior (D.tile j).carrier := by
    by_contra h
    exact hyF (mem_iUnion.mpr ⟨j, ⟨subset_closure hj, h⟩⟩)
  have hjS : j ∈ insideTiles D T' :=
    mem_insideTiles.mpr (tile_subset_of_interior_meet D T' hwall j ⟨y, hyj, hyV.2⟩)
  exact hyV.1 (mem_biUnion hjS hj)

/-- **The restricted tiling.** The tiles lying in `T'`, reindexed, tile `T'`, with the same
model tile. -/
noncomputable def CongruentDissection.restrict {N : ℕ} (D : CongruentDissection N) (T' : Tri)
    (hsub : T'.carrier ⊆ D.target.carrier)
    (hwall : ∀ y ∈ frontier T'.carrier, ∀ i, y ∉ interior (D.tile i).carrier) :
    CongruentDissection (insideTiles D.toDissection T').card where
  target := T'
  tile := fun k => D.tile ((insideTiles D.toDissection T').equivFin.symm k)
  covers := by
    rw [← insideTiles_cover D.toDissection T' hsub hwall]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨_, ((insideTiles D.toDissection T').equivFin.symm k).2, hk⟩
    · rintro ⟨i, hi, hx⟩
      exact ⟨(insideTiles D.toDissection T').equivFin ⟨i, hi⟩, by simpa using hx⟩
  interiors_disjoint := by
    intro k l hkl
    apply D.interiors_disjoint
    intro h
    exact hkl ((insideTiles D.toDissection T').equivFin.symm.injective (Subtype.ext h))
  model := D.model
  tiles_congruent := fun k => D.tiles_congruent _

/-- **Angle sums in the restricted tiling.** At every point, the local angles of the tiles lying
in `T'` sum to the local angle of `T'`. -/
theorem sum_localAngle_inside {N : ℕ} (D : CongruentDissection N) (T' : Tri)
    (hsub : T'.carrier ⊆ D.target.carrier)
    (hwall : ∀ y ∈ frontier T'.carrier, ∀ i, y ∉ interior (D.tile i).carrier) (p : Plane) :
    ∑ i ∈ insideTiles D.toDissection T', (D.tile i).localAngle p = T'.localAngle p := by
  have h := (CongruentDissection.restrict D T' hsub hwall).toDissection.sum_localAngle_eq p
  refine Eq.trans ?_ h
  show _ = ∑ k, (D.tile ((insideTiles D.toDissection T').equivFin.symm k)).localAngle p
  rw [← Finset.sum_coe_sort]
  exact (Equiv.sum_comp (insideTiles D.toDissection T').equivFin.symm
    (fun i => (D.tile i).localAngle p)).symm

end TriangleTiling
