/-
Angle counts for a right-angled tile `(α, β, π/2)` with `α` not a rational multiple of `π`
(Sections 5 and 6 of M. Beeson, *Tilings of an isosceles triangle*).

Then `β = π/2 - α`, and the values `α, β, π/2, π, 2π` are distinct and nonzero. At a point where
the target's local angle is `s α + t π/2`, the numbers of tiles with angle `α, β, π/2, π, 2π` there
satisfy `n_α - n_β = s` and `n_β + n_{π/2} + 2 n_π + 4 n_{2π} = t`. In particular, at every point
inside the target or inside one of its sides the `c` edges (hypotenuses) come in pairs.
-/
import TriangleTiling.Isosceles.MarkedCount
import TriangleTiling.Isosceles.GammaVertices

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

variable {N : ℕ} (D : CongruentDissection N)

theorem right_beta (hright : tileγ D = Real.pi / 2) : tileβ D = Real.pi / 2 - tileα D := by
  have h : tileα D + tileβ D + tileγ D = Real.pi := cornerAngle_sum D.model
  linarith

variable (hright : tileγ D = Real.pi / 2) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
include hright hirr

/-- The angle values of a right-angled tile are distinct and nonzero. -/
theorem anglesSep_right : AnglesSep D := by
  have hβ := right_beta D hright
  have hq : ∀ q : ℚ, tileα D ≠ (q : ℝ) * Real.pi := fun q h => hirr ⟨q, h⟩
  have hpi := Real.pi_pos
  refine ⟨fun j => ?_, fun i j h => ?_⟩
  · fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, ne_eq]
    · intro h; exact hq 0 (by push_cast; linarith)
    · intro h; exact hq (1 / 2) (by push_cast; linarith)
    · rw [hright]; positivity
    · positivity
    · positivity
  · fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h ⊢ <;>
      rw [hβ, hright] at * <;>
      first
      | rfl
      | (exfalso; linarith)
      | (exfalso; exact hq (1 / 4) (by push_cast; linarith))
      | (exfalso; exact hq (1 / 2) (by push_cast; linarith))
      | (exfalso; exact hq 1 (by push_cast; linarith))
      | (exfalso; exact hq 2 (by push_cast; linarith))
      | (exfalso; exact hq 0 (by push_cast; linarith))
      | (exfalso; exact hq (-1 / 2) (by push_cast; linarith))
      | (exfalso; exact hq (-3 / 2) (by push_cast; linarith))

/-- **The vertex relations for a right-angled tile.** -/
theorem vertex_relations_right (P : Plane) (s t : ℤ)
    (hP : D.target.localAngle P = s * tileα D + t * (Real.pi / 2)) :
    (angleCount D P (tileα D) : ℤ) - angleCount D P (tileβ D) = s ∧
    (angleCount D P (tileβ D) : ℤ) + angleCount D P (tileγ D) + 2 * angleCount D P Real.pi
      + 4 * angleCount D P (2 * Real.pi) = t := by
  obtain ⟨hv0, hinj⟩ := anglesSep_right D hright hirr
  have hβ := right_beta D hright
  have hf : ∀ i, (∃ j, (D.tile i).localAngle P =
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] j) ∨ (D.tile i).localAngle P = 0 := by
    intro i
    rcases localAngle_mem D P i with h | h | h | h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · exact Or.inl ⟨2, h⟩
    · exact Or.inl ⟨3, h⟩
    · exact Or.inl ⟨4, h⟩
    · exact Or.inr h
  have hcount := sum_eq_counts (fun i => (D.tile i).localAngle P) _ hv0 hinj hf
  rw [D.toDissection.sum_localAngle_eq P, Fin.sum_univ_five, hP] at hcount
  have hcount' : (angleCount D P (tileα D) : ℝ) * tileα D
      + (angleCount D P (tileβ D) : ℝ) * tileβ D + (angleCount D P (tileγ D) : ℝ) * tileγ D
      + (angleCount D P Real.pi : ℝ) * Real.pi
      + (angleCount D P (2 * Real.pi) : ℝ) * (2 * Real.pi) = s * tileα D + t * (Real.pi / 2) :=
    hcount.symm
  have key : (((2 * ((angleCount D P (tileα D) : ℤ) - angleCount D P (tileβ D) - s)) : ℤ) : ℝ)
      * tileα D + ((((angleCount D P (tileβ D) : ℤ) + angleCount D P (tileγ D)
        + 2 * angleCount D P Real.pi + 4 * angleCount D P (2 * Real.pi) - t) : ℤ) : ℝ)
        * Real.pi = 0 := by
    push_cast
    linear_combination 2 * hcount' - 2 * (angleCount D P (tileβ D) : ℝ) * hβ
      - 2 * (angleCount D P (tileγ D) : ℝ) * hright
  obtain ⟨h1, h2⟩ := angle_indep hirr _ _ key
  omega

open Classical in
/-- **Hypotenuses come in pairs** at a point inside the target or inside one of its sides. -/
theorem right_c_even {P : Plane} {t : ℤ}
    (hP : D.target.localAngle P = (0 : ℤ) * tileα D + t * (Real.pi / 2)) :
    Even ((edgesAt D.toDissection P).filter (edgeType D (tileγ D))).card := by
  have hcm := card_marked D (anglesSep_right D hright hirr) P (φ := tileγ D) (Or.inr (Or.inr rfl))
  obtain ⟨h1, -⟩ := vertex_relations_right D hright hirr P 0 t hP
  exact ⟨angleCount D P (tileβ D), by omega⟩

/-- At a vertex inside a side of the target, no tile has the vertex inside one of its edges. -/
theorem right_side_no_relint {Q : Plane} (hfr : Q ∈ frontier D.target.carrier)
    (hnc : Q ∉ Set.range D.target.pts) {i : Fin N} {k : Fin 3} (hik : (D.tile i).pts k = Q) :
    ∀ j : Fin N, ∀ m : Fin 3, Q ∉ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)) := by
  intro j m hQ
  have hloc : D.target.localAngle Q = (0 : ℤ) * tileα D + (2 : ℤ) * (Real.pi / 2) := by
    rw [D.target.localAngle_frontier hfr hnc]; push_cast; ring
  obtain ⟨h1, h2⟩ := vertex_relations_right D hright hirr Q 0 2 hloc
  have hπ := angleCount_pos D (Tri.localAngle_openSegment _ m hQ)
  have hpos := vertex_counts_pos D hik
  omega

end TriangleTiling
