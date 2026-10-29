/-
Two facts used repeatedly in `lemma:twocs`.

* A tile's corner angle at `V` is the angle at `V` between its other two vertices.
* **The supplementary angle.** Let a tile `T₁` have corners `V, W, R'` with angle `θ ∈ {α, β}` at
  `V`, and let `V` lie strictly between `X` and `W`. No tile has its `γ` at `V` with its other two
  vertices on the rays `VX` and `VR'`: that angle would be `π - θ`, which is not `γ`.
-/
import TriangleTiling.TwoCs.Geom

namespace TriangleTiling.TwoCs

open Erdos634.Geometry EuclideanGeometry Set

/-- A corner angle is the angle between the other two vertices. -/
theorem corner_angle_eq (T : Tri) {j j' j'' : Fin 3} (h1 : j' ≠ j) (h2 : j'' ≠ j)
    (h3 : j' ≠ j'') : T.localAngle (T.pts j) = ∠ (T.pts j') (T.pts j) (T.pts j'') := by
  rw [Tri.localAngle_vertex, cornerAngle]
  have : (j' = j + 1 ∧ j'' = j + 2) ∨ (j' = j + 2 ∧ j'' = j + 1) := by
    revert h1 h2 h3; fin_cases j <;> fin_cases j' <;> fin_cases j'' <;> simp
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact angle_comm _ _ _

variable {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D)

include hsep in
/-- **The supplementary angle.** -/
theorem supp_contra {T₁ T' : Fin N} {jV jW jR jV' j1 j2 : Fin 3} {V W R' X : Plane}
    (hd1 : jW ≠ jV) (hd2 : jR ≠ jV) (hd3 : jW ≠ jR)
    (hV : (D.tile T₁).pts jV = V) (hW : (D.tile T₁).pts jW = W) (hR : (D.tile T₁).pts jR = R')
    (hθ : (D.tile T₁).localAngle V = tileα D ∨ (D.tile T₁).localAngle V = tileβ D)
    (hX : ∠ X V W = Real.pi)
    (he1 : j1 ≠ jV') (he2 : j2 ≠ jV') (he3 : j1 ≠ j2) (hV' : (D.tile T').pts jV' = V)
    (hγV : (D.tile T').localAngle V = tileγ D)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (h1 : (D.tile T').pts j1 = AffineMap.lineMap V X s)
    (h2 : (D.tile T').pts j2 = AffineMap.lineMap V R' t) : False := by
  obtain ⟨hα, hβ, hγ0⟩ := angles_pos D hsep
  have hsum := tile_angle_sum D
  have e1 := corner_angle_eq (D.tile T') he1 he2 he3
  rw [hV', h1, h2, hγV, angle_ray ht, angle_comm, angle_ray hs, angle_comm] at e1
  have e2 := corner_angle_eq (D.tile T₁) hd1 hd2 hd3
  rw [hV, hW, hR] at e2
  have hs := angle_supp (Z := R') hX
  rw [angle_comm R' V W, ← e2, ← e1] at hs
  rcases hθ with h | h <;> rw [h] at hs <;> linarith

end TriangleTiling.TwoCs
