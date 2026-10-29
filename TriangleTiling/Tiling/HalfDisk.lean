/-
Next to a point inside an edge of a tile.

Moving from a point inside edge `m` of a tile `S` towards the side of `S` enters the interior of
`S`; so every other tile containing the point lies on the other closed side of the edge's line.
-/
import TriangleTiling.Tiling.Restrict
import TriangleTiling.Tiling.Links

namespace TriangleTiling

open Erdos634.Geometry Set

/-- Moving from a point inside edge `m` of `T` towards a point with positive `m + 2` coordinate
enters the interior of `T`. -/
theorem Tri.lineMap_mem_interior (T : Tri) (m : Fin 3) {Q Z : Plane}
    (hQ : Q ∈ openSegment ℝ (T.pts m) (T.pts (m + 1))) (hZ : 0 < T.basis.coord (m + 2) Z) :
    ∃ τ₀ > (0 : ℝ), ∀ τ, 0 < τ → τ < τ₀ → AffineMap.lineMap Q Z τ ∈ interior T.carrier := by
  obtain ⟨h0, h1, h2⟩ := Tri.coord_openSegment T m hQ
  obtain ⟨ε0, hε0, hε⟩ := exists_small_pos (b := T.basis.coord m Z - T.basis.coord m Q) h0
  obtain ⟨ε1, hε1, hε'⟩ :=
    exists_small_pos (b := T.basis.coord (m + 1) Z - T.basis.coord (m + 1) Q) h1
  refine ⟨min ε0 ε1, lt_min hε0 hε1, fun τ hτ hτ' => ?_⟩
  rw [Tri.mem_interior_iff_coord_pos]
  intro j
  rw [Tri.coord_lineMap]
  rcases fin3_cases3 j m with rfl | rfl | rfl
  · exact hε τ hτ (lt_of_lt_of_le hτ' (min_le_left _ _))
  · exact hε' τ hτ (lt_of_lt_of_le hτ' (min_le_right _ _))
  · rw [h2, sub_zero, zero_add]; exact mul_pos hτ hZ

/-- **Other tiles stay on the other side.** If `Q` is inside edge `m` of tile `j`, every other tile
containing `Q` has nonpositive `m + 2` coordinate (with respect to tile `j`) throughout. -/
theorem tile_side_of_openSegment {N : ℕ} (D : Dissection N) {j : Fin N} {m : Fin 3} {Q : Plane}
    (hQ : Q ∈ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)))
    {i : Fin N} (hij : i ≠ j) (hQi : Q ∈ (D.tile i).carrier) :
    ∀ z ∈ (D.tile i).carrier, (D.tile j).basis.coord (m + 2) z ≤ 0 := by
  intro z hz
  by_contra hpos
  push Not at hpos
  obtain ⟨τ0, hτ0, hint⟩ := Tri.lineMap_mem_interior (D.tile j) m hQ hpos
  set τ := min τ0 1 / 2
  have hτ : 0 < τ := by have := lt_min hτ0 one_pos; simp only [τ]; linarith
  have hττ : τ < τ0 := by have := min_le_left τ0 1; simp only [τ]; linarith
  have hτ1 : τ ≤ 1 := by have := min_le_right τ0 1; simp only [τ]; linarith
  have hyS := hint τ hτ hττ
  have hyT : AffineMap.lineMap Q z τ ∈ (D.tile i).carrier := by
    refine (D.tile i).convex.segment_subset hQi hz ?_
    rw [segment_eq_image_lineMap]
    exact ⟨τ, ⟨hτ.le, hτ1⟩, rfl⟩
  have hcl : AffineMap.lineMap Q z τ ∈ closure (interior (D.tile i).carrier) := by
    rw [tri_closure_interior]; exact hyT
  obtain ⟨w, hwS, hwT⟩ := mem_closure_iff.mp hcl _ isOpen_interior hyS
  exact Set.disjoint_left.mp (D.interiors_disjoint hij) hwT hwS

end TriangleTiling
