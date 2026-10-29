/-
Local geometry of a tiling: barycentric coordinates along sides, angles at a point of a line,
the local angle at a point inside an edge, and the first edge of a wall chain at an end of the
wall.
-/
import Erdos634.WallChain
import Erdos634.AngleSumDissection

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-! ### Barycentric coordinates -/

theorem Tri.basis_apply' (T : Tri) (j : Fin 3) : T.basis j = T.pts j := rfl

theorem Tri.coord_vertex (T : Tri) (i j : Fin 3) :
    T.basis.coord i (T.pts j) = if i = j then 1 else 0 := by
  rw [← Tri.basis_apply', AffineBasis.coord_apply]

theorem Tri.coord_lineMap (T : Tri) (i : Fin 3) (X Y : Plane) (t : ℝ) :
    T.basis.coord i (AffineMap.lineMap X Y t)
      = T.basis.coord i X + t * (T.basis.coord i Y - T.basis.coord i X) := by
  rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module']
  simp only [smul_eq_mul]; ring

theorem Tri.coord_sum (T : Tri) (X : Plane) :
    T.basis.coord 0 X + T.basis.coord 1 X + T.basis.coord 2 X = 1 := by
  have := T.basis.sum_coord_apply_eq_one X
  rw [Fin.sum_univ_three] at this; exact this

theorem Tri.mem_carrier_iff_coord (T : Tri) (X : Plane) :
    X ∈ T.carrier ↔ ∀ i, 0 ≤ T.basis.coord i X := by
  rw [T.carrier_eq_nonneg_coord]; rfl

/-! ### Angles at a point of a line -/

/-- If `P = lineMap Q Z s` and `Y = lineMap Q Z t` with `s, t ≠ 0`, then the angles at `Q`
from `R` to `P` and to `Y` are equal (same side of `Q`) or supplementary (opposite sides). -/
theorem angle_on_line {Q Z R : Plane} {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) :
    ∠ R Q (AffineMap.lineMap Q Z t) = ∠ R Q (AffineMap.lineMap Q Z s) ∨
    ∠ R Q (AffineMap.lineMap Q Z t) = Real.pi - ∠ R Q (AffineMap.lineMap Q Z s) := by
  have hv : ∀ r : ℝ, AffineMap.lineMap Q Z r -ᵥ Q = r • (Z -ᵥ Q) := by
    intro r; rw [AffineMap.lineMap_vsub_left]
  simp only [EuclideanGeometry.angle, hv]
  rcases lt_or_gt_of_ne hs with hs | hs <;> rcases lt_or_gt_of_ne ht with ht | ht
  · left
    rw [InnerProductGeometry.angle_smul_right_of_neg _ _ ht,
      InnerProductGeometry.angle_smul_right_of_neg _ _ hs]
  · right
    rw [InnerProductGeometry.angle_smul_right_of_pos _ _ ht,
      InnerProductGeometry.angle_smul_right_of_neg _ _ hs, InnerProductGeometry.angle_neg_right]
    ring
  · right
    rw [InnerProductGeometry.angle_smul_right_of_neg _ _ ht,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hs, InnerProductGeometry.angle_neg_right]
  · left
    rw [InnerProductGeometry.angle_smul_right_of_pos _ _ ht,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hs]

/-! ### The local angle inside an edge -/

/-- At a point strictly inside an edge, a tile's local angle is `π`. -/
theorem Tri.localAngle_openSegment (T : Tri) (m : Fin 3) {x : Plane}
    (hx : x ∈ openSegment ℝ (T.pts m) (T.pts (m + 1))) : T.localAngle x = Real.pi := by
  classical
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  have hm : T.basis.coord m (AffineMap.lineMap (T.pts m) (T.pts (m + 1)) t) = 1 - t := by
    rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m ≠ m + 1 by fin_cases m <;> decide]; ring
  have hm1 : T.basis.coord (m + 1) (AffineMap.lineMap (T.pts m) (T.pts (m + 1)) t) = t := by
    rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m + 1 ≠ m by fin_cases m <;> decide]
  have hm2 : T.basis.coord (m + 2) (AffineMap.lineMap (T.pts m) (T.pts (m + 1)) t) = 0 := by
    rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m + 2 ≠ m by fin_cases m <;> decide, show m + 2 ≠ m + 1 by fin_cases m <;> decide]
  set x := AffineMap.lineMap (T.pts m) (T.pts (m + 1)) t
  have hv : ¬ ∃ j, x = T.pts j := by
    rintro ⟨j, hj⟩
    have h1 := Tri.coord_vertex T m j
    have h2 := Tri.coord_vertex T (m + 1) j
    rw [← hj, hm] at h1
    rw [← hj, hm1] at h2
    split_ifs at h1 h2 <;> linarith
  have h2 : ¬ ∀ j, 0 < T.basis.coord j x := fun h => by have := h (m + 2); rw [hm2] at this; linarith
  have h3 : ∃ k, T.basis.coord k x = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j x := by
    refine ⟨m + 2, hm2, fun j hj => ?_⟩
    have : j = m ∨ j = m + 1 := by fin_cases m <;> fin_cases j <;> simp at hj ⊢
    rcases this with rfl | rfl
    · rw [hm]; linarith
    · rw [hm1]; exact ht0
  rw [Tri.localAngle, dif_neg hv, if_neg h2, if_pos h3]

/-! ### The first edge of a wall chain at an end of the wall -/

/-- **The chain edge at an end.** For a wall segment `VW` inside the tiled triangle, some edge of
the chain on the side `{f ≤ c}` contains `V` and also points of the open segment `VW`. -/
theorem exists_chain_edge_at {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hf : f ≠ 0) {V W : Plane} (hVW : V ≠ W) (hS : segment ℝ V W ⊆ {y | f y = c})
    (hint : openSegment ℝ V W ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ V W, ∀ i, y ∉ interior (D.tile i).carrier) :
    ∃ e ∈ D.lineChain f c, V ∈ (D.tile e.1).edge e.2 ∧
      ∃ x ∈ openSegment ℝ V W, x ∈ (D.tile e.1).edge e.2 := by
  classical
  set S := D.lineChain f c
  set bad := S.filter fun e => V ∉ (D.tile e.1).edge e.2
  have hpos : ∀ e ∈ bad, 0 < Metric.infDist V ((D.tile e.1).edge e.2) := by
    intro e he
    have hne : ((D.tile e.1).edge e.2).Nonempty := ⟨_, left_mem_segment ℝ _ _⟩
    exact ((D.tile e.1).isClosed_edge e.2).notMem_iff_infDist_pos hne |>.mp
      (Finset.mem_filter.mp he).2
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ e ∈ bad, δ ≤ Metric.infDist V ((D.tile e.1).edge e.2) := by
    by_cases hb : bad.Nonempty
    · refine ⟨bad.inf' hb fun e => Metric.infDist V ((D.tile e.1).edge e.2), ?_,
        fun e he => Finset.inf'_le _ he⟩
      exact (Finset.lt_inf'_iff hb).mpr hpos
    · exact ⟨1, one_pos, fun e he => absurd ⟨e, he⟩ hb⟩
  have hd : 0 < dist V W := dist_pos.mpr hVW
  set τ := min (1 / 2) (δ / (2 * dist V W)) with hτ
  have hτ0 : 0 < τ := lt_min (by norm_num) (by positivity)
  -- A non-vertex point of `VW` close to `V`.
  have hinf : (AffineMap.lineMap V W '' Set.Ioo (0 : ℝ) τ).Infinite :=
    (Set.Ioo_infinite hτ0).image (AffineMap.lineMap_injective ℝ hVW).injOn
  obtain ⟨x, ⟨⟨t, ⟨ht0, htτ⟩, rfl⟩, hxv⟩⟩ :=
    (hinf.diff D.vertexSet_finite).nonempty
  have ht1 : t < 1 := lt_of_lt_of_le htτ ((min_le_left _ _).trans (by norm_num))
  have hxo : AffineMap.lineMap V W t ∈ openSegment ℝ V W := by
    rw [openSegment_eq_image_lineMap]; exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
  obtain ⟨e, he, hxe⟩ := D.wall_cover f c hf hVW hS hint hwall hxo hxv
  refine ⟨e, he, ?_, _, hxo, hxe⟩
  by_contra hVe
  have hbad : e ∈ bad := Finset.mem_filter.mpr ⟨he, hVe⟩
  have h1 := Metric.infDist_le_dist_of_mem (x := V) hxe
  rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_pos ht0] at h1
  have h2 : t * dist V W < δ := by
    have : t < δ / (2 * dist V W) := lt_of_lt_of_le htτ (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith
  linarith [hδle e hbad]

end TriangleTiling
