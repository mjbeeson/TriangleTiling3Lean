/-
Plane geometry for `lemma:twocs`: open segments inside a triangle, angles along a ray and at a
point of a line, and the sides of the tile (`a < b < c` when `α < β` and `γ > π/2`).
-/
import TriangleTiling.TwoCs.Counts
import TriangleTiling.Isosceles.No28Support

namespace TriangleTiling.TwoCs

open Erdos634.Geometry EuclideanGeometry Set

/-- **An open segment inside a triangle.** If `X, Y` are in `T` and at each vertex one of them has
positive coordinate, the open segment `XY` is interior to `T`. -/
theorem openSegment_subset_interior (T : Tri) {X Y : Plane} (hX : X ∈ T.carrier)
    (hY : Y ∈ T.carrier) (h : ∀ k, 0 < T.basis.coord k X ∨ 0 < T.basis.coord k Y) :
    openSegment ℝ X Y ⊆ interior T.carrier := by
  intro z hz
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
  rw [Tri.mem_interior_iff_coord_pos]
  intro k
  rw [Tri.coord_lineMap]
  have hx := (Tri.mem_carrier_iff_coord T X).mp hX k
  have hy := (Tri.mem_carrier_iff_coord T Y).mp hY k
  rcases h k with h | h <;> nlinarith

/-- An interior point of `T`: every coordinate is positive. -/
theorem coord_pos_of_interior (T : Tri) {X : Plane} (hX : X ∈ interior T.carrier) (k : Fin 3) :
    0 < T.basis.coord k X :=
  (Tri.mem_interior_iff_coord_pos T X).mp hX k

/-- The angle toward a point of a ray does not depend on the point. -/
theorem angle_ray {X V Z : Plane} {t : ℝ} (ht : 0 < t) :
    ∠ X V (AffineMap.lineMap V Z t) = ∠ X V Z := by
  have := angle_on_line (Q := V) (Z := Z) (R := X) (s := 1) (t := t) one_ne_zero ht.ne'
  rw [AffineMap.lineMap_apply_one] at this
  rcases this with h | h
  · exact h
  · simp only [EuclideanGeometry.angle, AffineMap.lineMap_vsub_left]
    rw [InnerProductGeometry.angle_smul_right_of_pos _ _ ht]

/-- **Supplementary angles.** If `V` is strictly between `X` and `W` (`∠ X V W = π`), the angles at
`V` from `Z` to `X` and to `W` add up to `π`. -/
theorem angle_supp {X V W Z : Plane} (h : ∠ X V W = Real.pi) :
    ∠ X V Z + ∠ Z V W = Real.pi := by
  have := angle_add_angle_eq_pi_of_angle_eq_pi Z h
  rw [angle_comm Z V X] at this
  exact this

/-- `∠ X V W = π` for `V` strictly inside the segment `XW`. -/
theorem angle_eq_pi_of_mem_openSegment {X V W : Plane} (hXW : X ≠ W)
    (hV : V ∈ openSegment ℝ X W) : ∠ X V W = Real.pi := by
  rw [openSegment_eq_image_lineMap] at hV
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hV
  refine angle_eq_pi_iff_sbtw.mpr ⟨⟨t, ⟨ht0.le, ht1.le⟩, rfl⟩, ?_, ?_⟩
  · intro h
    have : AffineMap.lineMap X W t = AffineMap.lineMap X W (0 : ℝ) := by
      rw [h, AffineMap.lineMap_apply_zero]
    have := AffineMap.lineMap_injective ℝ hXW this
    linarith
  · intro h
    have : AffineMap.lineMap X W t = AffineMap.lineMap X W (1 : ℝ) := by
      rw [h, AffineMap.lineMap_apply_one]
    have := AffineMap.lineMap_injective ℝ hXW this
    linarith

section Model

variable {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D) (hγ : Real.pi / 2 < tileγ D)

include hsep hγ in
/-- **The sides of the tile.** With `α < β` and `γ > π/2`: `a < b < c`, where `a, b, c` are the
model's sides opposite `α, β, γ`. -/
theorem sides_lt (hαβ : tileα D < tileβ D) :
    dist (D.model.pts 1) (D.model.pts 2) < dist (D.model.pts 2) (D.model.pts 0) ∧
      dist (D.model.pts 2) (D.model.pts 0) < dist (D.model.pts 0) (D.model.pts 1) := by
  obtain ⟨hα, hβ, hγ0⟩ := angles_pos D hsep
  have hsum := tile_angle_sum D
  have hπ := Real.pi_pos
  set m := D.model
  have l1 := law_sin (m.pts 1) (m.pts 0) (m.pts 2)
  have l3 := law_sin (m.pts 2) (m.pts 1) (m.pts 0)
  have eα : ∠ (m.pts 1) (m.pts 0) (m.pts 2) = tileα D := rfl
  have eβ : ∠ (m.pts 2) (m.pts 1) (m.pts 0) = tileβ D := rfl
  have eγ : ∠ (m.pts 0) (m.pts 2) (m.pts 1) = tileγ D := rfl
  rw [eα, eβ] at l1
  rw [eβ, eγ] at l3
  have hsa : 0 < Real.sin (tileα D) := Real.sin_pos_of_pos_of_lt_pi hα (by linarith)
  have hsβ : Real.sin (tileα D) < Real.sin (tileβ D) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hαβ
  have hsγ : Real.sin (tileβ D) < Real.sin (tileγ D) := by
    rw [show tileγ D = Real.pi - (tileα D + tileβ D) by linarith, Real.sin_pi_sub]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hne : ∀ x y : Fin 3, x ≠ y → m.pts x ≠ m.pts y := fun x y h e => h (m.indep.injective e)
  have ha : 0 < dist (m.pts 1) (m.pts 2) := dist_pos.mpr (hne 1 2 (by decide))
  have hb : 0 < dist (m.pts 2) (m.pts 0) := dist_pos.mpr (hne 2 0 (by decide))
  have hc : 0 < dist (m.pts 0) (m.pts 1) := dist_pos.mpr (hne 0 1 (by decide))
  rw [dist_comm (m.pts 0) (m.pts 2), dist_comm (m.pts 2) (m.pts 1)] at l1
  rw [dist_comm (m.pts 1) (m.pts 0), dist_comm (m.pts 0) (m.pts 2)] at l3
  constructor
  · nlinarith [mul_pos hsa hb, mul_pos hsa ha]
  · nlinarith [mul_pos hsa hb, mul_pos hsa hc]

end Model

end TriangleTiling.TwoCs
