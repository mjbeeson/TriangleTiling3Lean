/-
Angle counts at a point, for `lemma:twocs` of M. Beeson, *Triangle tiling: the case
3α + 2β = π* (arXiv 1206.2229v4).

The tile is general: angles `α, β, γ` (the model's, at `model.pts 0, 1, 2`) with `γ > π/2` and
`α/β` irrational. At a point inside a side of `ABC` the local angles add up to `π`; if one of them
is `γ` they are exactly `α, β, γ`. At a corner of `ABC` whose angle is less than `γ`, no tile has
its `γ`, and no tile has the corner inside an edge.
-/
import TriangleTiling.Gamma120.CRelation
import TriangleTiling.Isosceles.TwoBeta
import TriangleTiling.Tiling.AngleFacts

namespace TriangleTiling.TwoCs

open Erdos634.Geometry

variable {N : ℕ} (D : CongruentDissection N)

/-- The three angles of the tile add up to `π`. -/
theorem tile_angle_sum : tileα D + tileβ D + tileγ D = Real.pi := by
  have := cornerAngle_sum D.model
  simp only [cornerAngle] at this
  unfold tileα tileβ tileγ
  linarith

/-- The counts of the local angles at `P`, weighted, add up to the target's local angle. -/
theorem counts_sum (hsep : AnglesSep D) (P : Plane) :
    (angleCount D P (tileα D) : ℝ) * tileα D + (angleCount D P (tileβ D) : ℝ) * tileβ D +
      (angleCount D P (tileγ D) : ℝ) * tileγ D + (angleCount D P Real.pi : ℝ) * Real.pi +
      (angleCount D P (2 * Real.pi) : ℝ) * (2 * Real.pi) = D.target.localAngle P := by
  classical
  obtain ⟨hv0, hinj⟩ := hsep
  have h := sum_eq_counts (fun i => (D.tile i).localAngle P)
    ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] hv0 hinj (by
      intro i
      rcases localAngle_mem D P i with h | h | h | h | h | h
      · exact Or.inl ⟨0, h⟩
      · exact Or.inl ⟨1, h⟩
      · exact Or.inl ⟨2, h⟩
      · exact Or.inl ⟨3, h⟩
      · exact Or.inl ⟨4, h⟩
      · exact Or.inr h)
  rw [D.sum_localAngle_eq, Fin.sum_univ_five] at h
  rw [h]
  simp only [angleCount, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four]
  convert rfl using 2

variable (hsep : AnglesSep D) (hγ : Real.pi / 2 < tileγ D)
  (hirr : ¬ ∃ q : ℚ, tileα D = (q : ℝ) * tileβ D)

include hsep in
theorem angles_pos : 0 < tileα D ∧ 0 < tileβ D ∧ 0 < tileγ D := by
  refine ⟨?_, ?_, ?_⟩
  · exact lt_of_le_of_ne (EuclideanGeometry.angle_nonneg _ _ _) (hsep.1 0).symm
  · exact lt_of_le_of_ne (EuclideanGeometry.angle_nonneg _ _ _) (hsep.1 1).symm
  · exact lt_of_le_of_ne (EuclideanGeometry.angle_nonneg _ _ _) (hsep.1 2).symm

include hsep hγ hirr in
/-- **At a point inside a side** where some tile has its `γ`: exactly one `α`, one `β`, one `γ`,
and nothing else. -/
theorem side_counts {V : Plane} (hV : V ∈ frontier D.target.carrier)
    (hVc : V ∉ Set.range D.target.pts) (h1 : 1 ≤ angleCount D V (tileγ D)) :
    angleCount D V (tileα D) = 1 ∧ angleCount D V (tileβ D) = 1 ∧
      angleCount D V (tileγ D) = 1 ∧ angleCount D V Real.pi = 0 ∧
        angleCount D V (2 * Real.pi) = 0 := by
  have hs := counts_sum D hsep V
  rw [D.target.localAngle_frontier hV hVc] at hs
  have hsum := tile_angle_sum D
  obtain ⟨hα, hβ, hγ0⟩ := angles_pos D hsep
  have hπ := Real.pi_pos
  set x := angleCount D V (tileα D)
  set y := angleCount D V (tileβ D)
  set z := angleCount D V (tileγ D)
  set u := angleCount D V Real.pi
  set w := angleCount D V (2 * Real.pi)
  have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have hy : (0 : ℝ) ≤ y := Nat.cast_nonneg _
  have hu : (0 : ℝ) ≤ u := Nat.cast_nonneg _
  have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast h1
  have hz : z = 1 := by
    by_contra hne
    have : (2 : ℝ) ≤ z := by exact_mod_cast (show 2 ≤ z by omega)
    nlinarith [mul_nonneg hx hα.le, mul_nonneg hy hβ.le]
  have hw0 : w = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ w := by exact_mod_cast (show 1 ≤ w by omega)
    nlinarith [mul_nonneg hx hα.le, mul_nonneg hy hβ.le, mul_nonneg hu hπ.le]
  have hu0 : u = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ u := by exact_mod_cast (show 1 ≤ u by omega)
    rw [hz, hw0] at hs
    push_cast at hs
    nlinarith [mul_nonneg hx hα.le, mul_nonneg hy hβ.le, mul_nonneg hw hπ.le]
  rw [hz, hw0, hu0] at hs
  push_cast at hs
  -- `x α + y β = α + β`.
  have hxy : ((x : ℝ) - 1) * tileα D = (1 - (y : ℝ)) * tileβ D := by linarith
  have hx1 : x = 1 := by
    by_contra hne
    apply hirr
    refine ⟨(1 - (y : ℚ)) / ((x : ℚ) - 1), ?_⟩
    have hne' : (x : ℝ) - 1 ≠ 0 := by
      intro h0; apply hne; exact_mod_cast (show (x : ℝ) = 1 by linarith)
    push_cast
    field_simp
    linarith
  rw [hx1] at hxy
  push_cast at hxy
  have hy1 : y = 1 := by
    have : (1 - (y : ℝ)) * tileβ D = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact_mod_cast (show (y : ℝ) = 1 by linarith)
    · exact absurd h hβ.ne'
  exact ⟨hx1, hy1, hz, hu0, hw0⟩

include hsep hγ in
/-- At a point inside a side, at most one tile has its `γ`, and none the point in its interior. -/
theorem side_le {V : Plane} (hV : V ∈ frontier D.target.carrier)
    (hVc : V ∉ Set.range D.target.pts) :
    angleCount D V (tileγ D) ≤ 1 ∧ angleCount D V (2 * Real.pi) = 0 := by
  have hs := counts_sum D hsep V
  rw [D.target.localAngle_frontier hV hVc] at hs
  obtain ⟨hα, hβ, hγ0⟩ := angles_pos D hsep
  have hπ := Real.pi_pos
  have hx : (0 : ℝ) ≤ angleCount D V (tileα D) := Nat.cast_nonneg _
  have hy : (0 : ℝ) ≤ angleCount D V (tileβ D) := Nat.cast_nonneg _
  have hz : (0 : ℝ) ≤ angleCount D V (tileγ D) := Nat.cast_nonneg _
  have hu : (0 : ℝ) ≤ angleCount D V Real.pi := Nat.cast_nonneg _
  have hw : (0 : ℝ) ≤ angleCount D V (2 * Real.pi) := Nat.cast_nonneg _
  constructor
  · by_contra hne
    have : (2 : ℝ) ≤ angleCount D V (tileγ D) := by exact_mod_cast (show 2 ≤ _ by omega)
    nlinarith [mul_nonneg hx hα.le, mul_nonneg hy hβ.le, mul_nonneg hu hπ.le,
      mul_nonneg hw hπ.le]
  · by_contra hne
    have : (1 : ℝ) ≤ angleCount D V (2 * Real.pi) := by exact_mod_cast (show 1 ≤ _ by omega)
    nlinarith [mul_nonneg hx hα.le, mul_nonneg hy hβ.le, mul_nonneg hu hπ.le,
      mul_nonneg hz hγ0.le]

include hsep hγ in
/-- **At a corner** of `ABC` whose angle is less than `γ`: no tile has its `γ` there, and none has
the corner inside an edge or in its interior. -/
theorem corner_counts (k : Fin 3) (hk : D.target.localAngle (D.target.pts k) < tileγ D) :
    angleCount D (D.target.pts k) (tileγ D) = 0 ∧ angleCount D (D.target.pts k) Real.pi = 0 ∧
      angleCount D (D.target.pts k) (2 * Real.pi) = 0 := by
  have hs := counts_sum D hsep (D.target.pts k)
  obtain ⟨hα, hβ, hγ0⟩ := angles_pos D hsep
  have hsum := tile_angle_sum D
  have hπ := Real.pi_pos
  have hx : (0 : ℝ) ≤ angleCount D (D.target.pts k) (tileα D) := Nat.cast_nonneg _
  have hy : (0 : ℝ) ≤ angleCount D (D.target.pts k) (tileβ D) := Nat.cast_nonneg _
  have hz : (0 : ℝ) ≤ angleCount D (D.target.pts k) (tileγ D) := Nat.cast_nonneg _
  have hu : (0 : ℝ) ≤ angleCount D (D.target.pts k) Real.pi := Nat.cast_nonneg _
  have hw : (0 : ℝ) ≤ angleCount D (D.target.pts k) (2 * Real.pi) := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · by_contra hne
    have : (1 : ℝ) ≤ angleCount D (D.target.pts k) (tileγ D) := by
      exact_mod_cast (show 1 ≤ _ by omega)
    nlinarith [mul_nonneg hx hα.le, mul_nonneg hy hβ.le, mul_nonneg hu hπ.le,
      mul_nonneg hw hπ.le]
  · by_contra hne
    have : (1 : ℝ) ≤ angleCount D (D.target.pts k) Real.pi := by
      exact_mod_cast (show 1 ≤ _ by omega)
    nlinarith [mul_nonneg hx hα.le, mul_nonneg hy hβ.le, mul_nonneg hz hγ0.le,
      mul_nonneg hw hπ.le]
  · by_contra hne
    have : (1 : ℝ) ≤ angleCount D (D.target.pts k) (2 * Real.pi) := by
      exact_mod_cast (show 1 ≤ _ by omega)
    nlinarith [mul_nonneg hx hα.le, mul_nonneg hy hβ.le, mul_nonneg hz hγ0.le,
      mul_nonneg hu hπ.le]

end TriangleTiling.TwoCs
