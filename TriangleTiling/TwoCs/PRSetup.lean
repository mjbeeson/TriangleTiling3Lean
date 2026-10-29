/-
The wall along an edge `PR` of a tile, for `lemma:twocs`: a level line `{g = c}` through `P` and
`R` with the tile's third vertex `Q` strictly on the side `g > c`, and the fact that the open edge
meets no tile's interior.
-/
import TriangleTiling.TwoCs.WallGamma
import TriangleTiling.TwoCs.SideData
import TriangleTiling.Tiling.HalfDisk

namespace TriangleTiling.TwoCs

open Erdos634.Geometry EuclideanGeometry Set

/-- A vertex of a triangle is not on the line through the other two. -/
theorem vertex_ne_lineMap (T : Tri) {j j' j'' : Fin 3} (h1 : j' ≠ j) (h2 : j'' ≠ j) (t : ℝ) :
    T.pts j ≠ AffineMap.lineMap (T.pts j') (T.pts j'') t := by
  intro h
  have := congrArg (T.basis.coord j) h
  rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex, Tri.coord_vertex] at this
  simp [h1.symm, h2.symm] at this

/-- **The level line of an edge.** -/
theorem edge_level (T : Tri) {jP jQ jR : Fin 3} (hPQ : jQ ≠ jP) (hPR : jR ≠ jP)
    (hQR : jQ ≠ jR) :
    ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ g (T.pts jP) = c ∧ g (T.pts jR) = c ∧
      c < g (T.pts jQ) := by
  have hne : T.pts jR ≠ T.pts jP := fun h => hPR (T.indep.injective h)
  obtain ⟨g, c, hg, hgP, hgR⟩ := ray_level hne
  have hQ : g (T.pts jQ) ≠ c := by
    intro hQ
    obtain ⟨t, ht⟩ := eq_lineMap_of_level hg hne.symm hgP hgR hQ
    exact vertex_ne_lineMap T hPQ.symm hQR.symm t ht
  rcases lt_or_gt_of_ne hQ with h | h
  · refine ⟨-g, -c, neg_ne_zero.mpr hg, by simp [hgP], by simp [hgR], ?_⟩
    simp only [LinearMap.neg_apply, neg_lt_neg_iff]; exact h
  · exact ⟨g, c, hg, hgP, hgR, h⟩

/-- **The open edge is in no tile's interior.** -/
theorem openEdge_not_interior {N : ℕ} (D : Dissection N) (T₁ : Fin N) (m : Fin 3) :
    ∀ y ∈ openSegment ℝ ((D.tile T₁).pts m) ((D.tile T₁).pts (m + 1)), ∀ i,
      y ∉ interior (D.tile i).carrier := by
  intro y hy i hi
  have hc := (Tri.coord_openSegment (D.tile T₁) m hy).2.2
  by_cases hiT : i = T₁
  · subst hiT
    have := (Tri.mem_interior_iff_coord_pos _ y).mp hi (m + 2)
    linarith
  · have hside := tile_side_of_openSegment D hy hiT (interior_subset hi)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hi
    set Z := (D.tile T₁).pts (m + 2)
    have hyZ : 0 < dist y Z + 1 := by positivity
    set τ := ε / (2 * (dist y Z + 1))
    have hτ : 0 < τ := by positivity
    have hz : AffineMap.lineMap y Z τ ∈ interior (D.tile i).carrier := by
      apply hball
      rw [Metric.mem_ball, dist_comm, dist_left_lineMap, Real.norm_eq_abs, abs_of_pos hτ]
      calc τ * dist y Z ≤ τ * (dist y Z + 1) := by nlinarith
        _ = ε / 2 := by simp only [τ]; field_simp
        _ < ε := by linarith
    have := hside _ (interior_subset hz)
    rw [Tri.coord_lineMap, hc, Tri.coord_vertex, if_pos rfl] at this
    linarith

end TriangleTiling.TwoCs
