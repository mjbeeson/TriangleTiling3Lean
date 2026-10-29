/-
Corners and edges of a single tile, for `lemma:twocs`: each tile has one corner of each of the
angles `α, β, γ`, and its edge opposite the angle `θ` has the length of the model's side opposite
`θ`. (General versions of the isosceles project's `corner_unique` etc., which assumed `γ = 2α`.)
-/
import TriangleTiling.TwoCs.Counts
import TriangleTiling.RightTile.Helper2

namespace TriangleTiling.TwoCs

open Erdos634.Geometry

variable {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D)
include hsep

/-- A tile has its angle `θ` (one of `α, β, γ`) at exactly one vertex. -/
theorem corner_unique (i : Fin N) {θ : ℝ} (hθ : θ = tileα D ∨ θ = tileβ D ∨ θ = tileγ D)
    {j j' : Fin 3} (hj : (D.tile i).localAngle ((D.tile i).pts j) = θ)
    (hj' : (D.tile i).localAngle ((D.tile i).pts j') = θ) : j = j' := by
  rw [Tri.localAngle_vertex] at hj hj'
  have hcnt := tile_angle_count_sep D hsep i
  have hcard : (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
      ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = θ).card ≤ 1 := by
    rcases hθ with rfl | rfl | rfl
    · exact hcnt.1.le
    · exact hcnt.2.1.le
    · exact hcnt.2.2.le
  exact Finset.card_le_one.mp hcard j (by simp [hj]) j' (by simp [hj'])

/-- A tile has its angle `θ` (one of `α, β, γ`) at some vertex. -/
theorem corner_exists (i : Fin N) {θ : ℝ} (hθ : θ = tileα D ∨ θ = tileβ D ∨ θ = tileγ D) :
    ∃ j : Fin 3, (D.tile i).localAngle ((D.tile i).pts j) = θ := by
  have hcnt := tile_angle_count_sep D hsep i
  have hcard : (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
      ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = θ).card = 1 := by
    rcases hθ with rfl | rfl | rfl
    · exact hcnt.1
    · exact hcnt.2.1
    · exact hcnt.2.2
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have : j ∈ Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
      ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = θ := by rw [hj]; simp
  exact ⟨j, by rw [Tri.localAngle_vertex]; exact (Finset.mem_filter.mp this).2⟩

/-- Every corner angle of a tile is `α`, `β` or `γ`. -/
theorem corner_mem (i : Fin N) (j : Fin 3) :
    (D.tile i).localAngle ((D.tile i).pts j) = tileα D ∨
      (D.tile i).localAngle ((D.tile i).pts j) = tileβ D ∨
        (D.tile i).localAngle ((D.tile i).pts j) = tileγ D := by
  obtain ⟨ja, ha⟩ := corner_exists D hsep i (Or.inl rfl)
  obtain ⟨jb, hb⟩ := corner_exists D hsep i (Or.inr (Or.inl rfl))
  obtain ⟨jc, hc⟩ := corner_exists D hsep i (Or.inr (Or.inr rfl))
  have hne : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hsep.2.ne h
  have hab : ja ≠ jb := by
    rintro rfl; exact hne 0 1 (by decide) (ha.symm.trans hb)
  have hac : ja ≠ jc := by
    rintro rfl; exact hne 0 2 (by decide) (ha.symm.trans hc)
  have hbc : jb ≠ jc := by
    rintro rfl; exact hne 1 2 (by decide) (hb.symm.trans hc)
  have : j = ja ∨ j = jb ∨ j = jc := by
    revert hab hac hbc; fin_cases j <;> fin_cases ja <;> fin_cases jb <;> fin_cases jc <;> simp
  rcases this with rfl | rfl | rfl
  · exact Or.inl ha
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr hc)

/-- If a tile's angle opposite edge `k` is not `θ`, its `θ` is at an end of edge `k`. -/
theorem corner_at_endpoint (i : Fin N) (k : Fin 3) {θ : ℝ}
    (hθ : θ = tileα D ∨ θ = tileβ D ∨ θ = tileγ D)
    (hopp : (D.tile i).localAngle ((D.tile i).pts (k + 2)) ≠ θ) :
    (D.tile i).localAngle ((D.tile i).pts k) = θ ∨
      (D.tile i).localAngle ((D.tile i).pts (k + 1)) = θ := by
  obtain ⟨j, hj⟩ := corner_exists D hsep i hθ
  have : j = k ∨ j = k + 1 ∨ j = k + 2 := by fin_cases j <;> fin_cases k <;> simp
  rcases this with rfl | rfl | rfl
  · exact Or.inl hj
  · exact Or.inr hj
  · exact absurd hj hopp

omit hsep in
/-- The model's corner angle at `k` is the `k`-th of `α, β, γ`. -/
theorem model_corner' (k : Fin 3) :
    cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) =
      ![tileα D, tileβ D, tileγ D] k := by
  fin_cases k <;> rfl

/-- **Edge lengths.** The edge `k` of a tile, opposite its corner `k + 2`, has the length of the
model's side opposite the model's corner with the same angle. -/
theorem edge_length (i : Fin N) (k : Fin 3) (m : Fin 3)
    (h : (D.tile i).localAngle ((D.tile i).pts (k + 2)) = ![tileα D, tileβ D, tileγ D] m) :
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) =
      dist (D.model.pts (m + 1)) (D.model.pts (m + 2)) := by
  obtain ⟨σ, hang, hdist⟩ := corner_perm_dist (D.tiles_congruent i)
  rw [Tri.localAngle_vertex] at h
  have hk := hang (k + 2)
  rw [h, ← model_corner' D] at hk
  have hinj : ∀ x y : Fin 3, cornerAngle (D.model.pts (x + 1)) (D.model.pts x) (D.model.pts (x + 2))
      = cornerAngle (D.model.pts (y + 1)) (D.model.pts y) (D.model.pts (y + 2)) → x = y := by
    intro x y hxy
    rw [model_corner', model_corner'] at hxy
    have : (![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] (x.castLE (by norm_num)))
        = ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] (y.castLE (by norm_num)) := by
      fin_cases x <;> fin_cases y <;> first | rfl | simpa using hxy
    exact Fin.castLE_injective _ (hsep.2 this)
  have hσ : σ (k + 2) = m := hinj _ _ hk
  rw [hdist]
  have h1 : σ k ≠ σ (k + 2) := σ.injective.ne (by fin_cases k <;> decide)
  have h2 : σ (k + 1) ≠ σ (k + 2) := σ.injective.ne (by fin_cases k <;> decide)
  have h3 : σ k ≠ σ (k + 1) := σ.injective.ne (by fin_cases k <;> decide)
  rw [hσ] at h1 h2
  have : (σ k = m + 1 ∧ σ (k + 1) = m + 2) ∨ (σ k = m + 2 ∧ σ (k + 1) = m + 1) := by
    revert h1 h2 h3; generalize σ k = x; generalize σ (k + 1) = y
    fin_cases m <;> fin_cases x <;> fin_cases y <;> simp
  rcases this with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]
  · rw [e1, e2, dist_comm]

end TriangleTiling.TwoCs
