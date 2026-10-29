/-
Lines through a tiling, for `lemma:no28`: parameters along a line, coordinates at a point inside
an edge, a level line in a tile's coordinates, and points just beyond an edge-interior point.
-/
import TriangleTiling.Isosceles.No28Support
import TriangleTiling.Tiling.WallSum

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-! ### Parameters along a line -/

theorem lineMap_mem_segment_iff {U V : Plane} (hUV : U ≠ V) {τ a b : ℝ} :
    AffineMap.lineMap U V τ ∈ segment ℝ (AffineMap.lineMap U V a) (AffineMap.lineMap U V b) ↔
      τ ∈ segment ℝ a b := by
  rw [← image_segment]
  exact (AffineMap.lineMap_injective ℝ hUV).mem_set_image

/-- A segment between parameters in `[0, 1]` lies in `UV`. -/
theorem segment_param_subset {U V : Plane} {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    segment ℝ (AffineMap.lineMap U V a) (AffineMap.lineMap U V b) ⊆ segment ℝ U V := by
  have hu : AffineMap.lineMap U V a ∈ segment ℝ U V := by
    rw [segment_eq_image_lineMap]; exact ⟨a, ha, rfl⟩
  have hv : AffineMap.lineMap U V b ∈ segment ℝ U V := by
    rw [segment_eq_image_lineMap]; exact ⟨b, hb, rfl⟩
  exact (convex_segment (𝕜 := ℝ) U V).segment_subset hu hv

/-- A segment between parameters `≥ 1` meets `UV` in at most one point. -/
theorem segment_param_inter_subsingleton {U V : Plane} (hUV : U ≠ V) {a b : ℝ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    (segment ℝ (AffineMap.lineMap U V a) (AffineMap.lineMap U V b) ∩ segment ℝ U V).Subsingleton := by
  have key : ∀ y ∈ segment ℝ (AffineMap.lineMap U V a) (AffineMap.lineMap U V b) ∩ segment ℝ U V,
      y = V := by
    rintro y ⟨hy1, hy2⟩
    rw [segment_eq_image_lineMap] at hy2
    obtain ⟨t, ht, rfl⟩ := hy2
    rw [lineMap_mem_segment_iff hUV, segment_eq_uIcc] at hy1
    have : 1 ≤ t := by rcases Set.mem_uIcc.mp hy1 with h | h <;> linarith [h.1]
    rw [show t = 1 by linarith [ht.2], AffineMap.lineMap_apply_one]
  intro x hx y hy
  rw [key x hx, key y hy]

/-- Points of the triangle on the line from a point `Q` of side `AB` through a point `R` off
`AB` lie on the ray from `Q` through `R`. -/
theorem param_nonneg_of_side (T : Tri) {Q R : Plane} (hQ : Q ∈ segment ℝ (T.pts 0) (T.pts 1))
    (hR : 0 < T.basis.coord 2 R) {τ : ℝ} (hτ : AffineMap.lineMap Q R τ ∈ T.carrier) : 0 ≤ τ := by
  have h := (Tri.mem_carrier_iff_coord T _).mp hτ 2
  rw [Tri.coord_lineMap, coord_two_of_mem_side T hQ] at h
  nlinarith

/-! ### Coordinates inside an edge -/

theorem Tri.coord_openSegment (T : Tri) (m : Fin 3) {x : Plane}
    (hx : x ∈ openSegment ℝ (T.pts m) (T.pts (m + 1))) :
    0 < T.basis.coord m x ∧ 0 < T.basis.coord (m + 1) x ∧ T.basis.coord (m + 2) x = 0 := by
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m ≠ m + 1 by fin_cases m <;> decide]; linarith
  · rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m + 1 ≠ m by fin_cases m <;> decide]; exact ht0
  · rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m + 2 ≠ m by fin_cases m <;> decide, show m + 2 ≠ m + 1 by fin_cases m <;> decide]

theorem fin3_cases3 : ∀ j k : Fin 3, j = k ∨ j = k + 1 ∨ j = k + 2 := by decide

/-! ### A level line in a tile's coordinates -/

/-- If the linear functional `g` takes the value `c` at the vertices `k + 1, k + 2` of a tile,
then `g Y - c = coord_k Y · (g (pts k) - c)`. -/
theorem level_eq_coord (T : Tri) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (k : Fin 3)
    (h1 : g (T.pts (k + 1)) = c) (h2 : g (T.pts (k + 2)) = c) (Y : Plane) :
    g Y - c = T.basis.coord k Y * (g (T.pts k) - c) := by
  have hY := T.basis.linear_combination_coord_eq_self Y
  have hs := T.basis.sum_coord_apply_eq_one Y
  have hgY : g Y = ∑ i, T.basis.coord i Y * g (T.pts i) := by
    conv_lhs => rw [← hY]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]; rfl
  have hc : c = ∑ i, T.basis.coord i Y * c := by rw [← Finset.sum_mul, hs, one_mul]
  have e3 : ∀ i : Fin 3, i = k ∨ i = k + 1 ∨ i = k + 2 := fun i => fin3_cases3 i k
  rw [hgY]
  conv_lhs => rw [hc]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single k]
  · ring
  · intro i _ hik
    rcases e3 i with h | h | h
    · exact absurd h hik
    · rw [h, h1]; ring
    · rw [h, h2]; ring
  · simp

/-! ### Small ε -/

theorem exists_small_pos {a b : ℝ} (ha : 0 < a) :
    ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → 0 < a + ε * b := by
  by_cases hb : 0 ≤ b
  · exact ⟨1, one_pos, fun ε hε _ => by nlinarith⟩
  · push Not at hb
    refine ⟨a / (-b), div_pos ha (by linarith), fun ε hε hlt => ?_⟩
    rw [lt_div_iff₀ (by linarith)] at hlt
    nlinarith

/-! ### Orienting the line of a tile edge -/

/-- The line of edge `m` of a tile, as a level set `{g = c}` with the third vertex on the side
`g > c`. -/
theorem edge_level_oriented (T : Tri) (m : Fin 3) :
    ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ (∀ y ∈ T.edge m, g y = c) ∧ c < g (T.pts (m + 2)) := by
  obtain ⟨f, c, hf, hline⟩ := T.edge_line m
  have h1 : f (T.pts m) = c := hline _ (left_mem_segment _ _ _)
  have h2 : f (T.pts (m + 1)) = c := hline _ (right_mem_segment _ _ _)
  have hne : f (T.pts (m + 2)) ≠ c := by
    intro h3
    apply hf
    have hall : ∀ Y, f Y = c := by
      intro Y
      have := level_eq_coord T f c (m + 2) (by rw [fin3_add_two_add_one]; exact h1)
        (by rw [fin3_add_two_add_two]; exact h2) Y
      rw [h3, sub_self, mul_zero] at this; linarith
    have hc : c = 0 := by rw [← hall 0, map_zero]
    ext Y; simp [hall Y, hc]
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨-f, -c, neg_ne_zero.mpr hf, fun y hy => by simp [hline y hy], ?_⟩
    simp only [LinearMap.neg_apply]; linarith
  · exact ⟨f, c, hf, hline, h⟩

/-- No edge of the chain `{g ≤ c}` belongs to a tile with a vertex strictly on the side `g > c`. -/
theorem lineChain_tile_ne {N : ℕ} (D : Dissection N) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) {i : Fin N}
    {j : Fin 3} (hij : c < g ((D.tile i).pts j)) :
    ∀ e ∈ D.lineChain g c, e.1 ≠ i := by
  intro e he h
  obtain ⟨-, -, hall⟩ := Dissection.mem_lineChain.mp he
  have := hall j
  rw [h] at this
  linarith

/-- The edges of the chain `{g ≤ c}` on the line through `Q` (on side `AB`) and `R` (off `AB`)
have endpoints `lineMap Q R τ` with `τ ≥ 0`. -/
theorem lineChain_params {N : ℕ} (D : Dissection N) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hg : g ≠ 0)
    {Q R : Plane} (hQR : Q ≠ R) (hgQ : g Q = c) (hgR : g R = c)
    (hQ : Q ∈ segment ℝ (D.target.pts 0) (D.target.pts 1))
    (hR : 0 < D.target.basis.coord 2 R) (e : Fin N × Fin 3) (he : e ∈ D.lineChain g c) :
    ∃ τu τv : ℝ, 0 ≤ τu ∧ 0 ≤ τv ∧ (D.tile e.1).pts e.2 = AffineMap.lineMap Q R τu ∧
      (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap Q R τv := by
  obtain ⟨hu, hv, -⟩ := Dissection.mem_lineChain.mp he
  obtain ⟨τu, hτu⟩ := eq_lineMap_of_level hg hQR hgQ hgR hu
  obtain ⟨τv, hτv⟩ := eq_lineMap_of_level hg hQR hgQ hgR hv
  have htgt : ∀ (i : Fin N) (j : Fin 3), (D.tile i).pts j ∈ D.target.carrier := by
    intro i j
    have : (D.tile i).pts j ∈ (D.tile i).carrier := subset_convexHull ℝ _ ⟨j, rfl⟩
    rw [← D.covers]; exact Set.mem_iUnion.mpr ⟨i, this⟩
  refine ⟨τu, τv, ?_, ?_, hτu, hτv⟩
  · exact param_nonneg_of_side D.target hQ hR (hτu ▸ htgt _ _)
  · exact param_nonneg_of_side D.target hQ hR (hτv ▸ htgt _ _)

/-- A point of an edge where the tile's local angle is not `π` is an end of the edge. -/
theorem endpoint_of_ne_pi (X : Tri) (m : Fin 3) {V : Plane} (hV : V ∈ X.edge m)
    (hpi : X.localAngle V ≠ Real.pi) : V = X.pts m ∨ V = X.pts (m + 1) := by
  by_contra h
  push Not at h
  exact hpi (Tri.localAngle_openSegment X m
    (mem_openSegment_of_ne_left_right h.1.symm h.2.symm hV))

/-- The corner of a tile at a point `V` of the line `AB`, with another vertex `Y` on that line
and a third vertex on the ray from `V` through `R`: it equals `∠ZVR` or `π - ∠ZVR`, for any
other point `Z` of the line. -/
theorem corner_from_line (X : Tri) {jV jY jW : Fin 3} (h1 : jY ≠ jV) (h2 : jW ≠ jV)
    (h3 : jY ≠ jW) {A B R : Plane} {v y z w : ℝ}
    (hV : X.pts jV = AffineMap.lineMap A B v) (hY : X.pts jY = AffineMap.lineMap A B y)
    (hW : X.pts jW = AffineMap.lineMap (AffineMap.lineMap A B v) R w) (hw : 0 < w)
    (hyv : y ≠ v) (hzv : z ≠ v) :
    cornerAngle (X.pts (jV + 1)) (X.pts jV) (X.pts (jV + 2))
        = ∠ (AffineMap.lineMap A B z) (AffineMap.lineMap A B v) R ∨
      cornerAngle (X.pts (jV + 1)) (X.pts jV) (X.pts (jV + 2))
        = Real.pi - ∠ (AffineMap.lineMap A B z) (AffineMap.lineMap A B v) R := by
  rw [corner_eq_of_two X jV jY jW h1 h2 h3, hV, hY, hW]
  set V := AffineMap.lineMap A B v
  have hYW : ∠ (AffineMap.lineMap A B y) V (AffineMap.lineMap V R w)
      = ∠ (AffineMap.lineMap A B y) V R := by
    simp only [EuclideanGeometry.angle]
    rw [AffineMap.lineMap_vsub_left, InnerProductGeometry.angle_smul_right_of_pos _ _ hw]
  rw [hYW, angle_comm, angle_comm (AffineMap.lineMap A B z)]
  exact angle_on_line' hyv hzv

end TriangleTiling
