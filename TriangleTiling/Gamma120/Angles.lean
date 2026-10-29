/-
Angle counts for the tile `(α, β, 2π/3)` (Section 11 of M. Beeson, *Tilings of an isosceles
triangle*).

With `γ = 2π/3` and `α ∉ ℚπ` we have `β = π/3 - α`, and the values `α, β, γ, π, 2π` are distinct
and nonzero. At a point `P` where the target's local angle is `s α + t π`, the numbers
`n₀, n₁, n₂, n₃, n₄` of tiles with local angle `α, β, γ, π, 2π` there satisfy
`n₀ - n₁ = s` and `n₁ + 2 n₂ + 3 n₃ + 6 n₄ = 3 t` (`vertex_relations120`).

So at a point inside the target or inside a side, `n₀ = n₁`: the `α` and `β` angles there pair
up (this is the paper's table of vertex types). At the base corners `A`, `C` (angle `α`) there is
one tile, with its `α`; at the apex `B` (angle `π - 2α = α + 3β`) there are four, one `α` and
three `β`.
-/
import TriangleTiling.Isosceles.GammaStart
import TriangleTiling.Isosceles.No28Support
import TriangleTiling.Isosceles.LengthRelations

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

variable {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * Real.pi / 3)
  (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)

include hγ hirr

/-- `β = π/3 - α`, and `α, β, γ, π, 2π` are distinct and nonzero. -/
theorem angle_values120 : tileβ D = Real.pi / 3 - tileα D ∧ AnglesSep D := by
  set α := tileα D
  set β := tileβ D
  set γ := tileγ D
  have hsum3 : α + β + γ = Real.pi := cornerAngle_sum D.model
  have hβ : β = Real.pi / 3 - α := by linarith
  have hpi := Real.pi_pos
  -- `p α ≠ (q/3) π` for `p ≠ 0`.
  have hne : ∀ p q : ℤ, p ≠ 0 → 3 * (p : ℝ) * α ≠ q * Real.pi := by
    intro p q hp h
    exact hp (by
      have := (angle_indep hirr (3 * p) (-q) (by push_cast; linarith)).1
      omega)
  refine ⟨hβ, ?_, ?_⟩
  · intro j; fin_cases j
    · exact fun h => hne 1 0 one_ne_zero (by simp at h ⊢; linarith)
    · exact fun h => hne 1 1 one_ne_zero (by simp at h; push_cast; linarith)
    · change γ ≠ 0; rw [hγ]; positivity
    · simp [hpi.ne']
    · simp [hpi.ne']
  · intro j k hjk
    fin_cases j <;> fin_cases k <;> simp at hjk ⊢
    all_goals first
      | (exfalso; linarith)
      | exact hne 2 1 (by norm_num) (by push_cast; linarith)
      | exact hne 1 2 one_ne_zero (by push_cast; linarith)
      | exact hne 1 3 one_ne_zero (by push_cast; linarith)
      | exact hne 1 6 one_ne_zero (by push_cast; linarith)
      | exact hne 1 (-1) one_ne_zero (by push_cast; linarith)
      | exact hne 1 (-2) one_ne_zero (by push_cast; linarith)
      | exact hne 1 (-5) one_ne_zero (by push_cast; linarith)

omit hγ hirr in
/-- The arithmetic behind the vertex counts. -/
theorem counts_arith120 {α β γ : ℝ} (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hβ : β = Real.pi / 3 - α) (hγ : γ = 2 * Real.pi / 3) (n₀ n₁ n₂ n₃ n₄ : ℕ) (s t : ℤ)
    (h : (n₀ : ℝ) * α + n₁ * β + n₂ * γ + n₃ * Real.pi + n₄ * (2 * Real.pi) = s * α + t * Real.pi) :
    (n₀ : ℤ) - n₁ = s ∧ (n₁ : ℤ) + 2 * n₂ + 3 * n₃ + 6 * n₄ = 3 * t := by
  subst hβ hγ
  have key : ((3 * ((n₀ : ℤ) - n₁ - s) : ℤ) : ℝ) * α
      + (((n₁ : ℤ) + 2 * n₂ + 3 * n₃ + 6 * n₄ - 3 * t : ℤ) : ℝ) * Real.pi = 0 := by
    push_cast; linear_combination 3 * h
  obtain ⟨h1, h2⟩ := angle_indep hirr _ _ key
  omega

/-- **The vertex relations** for `γ = 2π/3`. -/
theorem vertex_relations120 (P : Plane) (s t : ℤ)
    (hP : D.target.localAngle P = s * tileα D + t * Real.pi) :
    (angleCount D P (tileα D) : ℤ) - angleCount D P (tileβ D) = s ∧
    (angleCount D P (tileβ D) : ℤ) + 2 * angleCount D P (tileγ D) + 3 * angleCount D P Real.pi
      + 6 * angleCount D P (2 * Real.pi) = 3 * t := by
  obtain ⟨hβ, hv0, hinj⟩ := angle_values120 D hγ hirr
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
      + (angleCount D P (2 * Real.pi) : ℝ) * (2 * Real.pi) = s * tileα D + t * Real.pi :=
    hcount.symm
  exact counts_arith120 hirr hβ hγ _ _ _ _ _ s t hcount'

/-- At a point inside the target, or inside a side, the `α` and `β` angles pair up. -/
theorem counts_noncorner {P : Plane} (hP : P ∈ D.target.carrier)
    (hPc : P ∉ Set.range D.target.pts) :
    angleCount D P (tileα D) = angleCount D P (tileβ D) ∧
      ((P ∈ interior D.target.carrier ∧ (angleCount D P (tileβ D) : ℤ)
          + 2 * angleCount D P (tileγ D) + 3 * angleCount D P Real.pi
          + 6 * angleCount D P (2 * Real.pi) = 6) ∨
        (P ∈ frontier D.target.carrier ∧ (angleCount D P (tileβ D) : ℤ)
          + 2 * angleCount D P (tileγ D) + 3 * angleCount D P Real.pi
          + 6 * angleCount D P (2 * Real.pi) = 3)) := by
  by_cases hint : P ∈ interior D.target.carrier
  · have := vertex_relations120 D hγ hirr P 0 2
      (by rw [D.target.localAngle_interior hint]; push_cast; ring)
    exact ⟨by omega, Or.inl ⟨hint, by omega⟩⟩
  · have hfr : P ∈ frontier D.target.carrier := ⟨subset_closure hP, hint⟩
    have := vertex_relations120 D hγ hirr P 0 1
      (by rw [D.target.localAngle_frontier hfr hPc]; push_cast; ring)
    exact ⟨by omega, Or.inr ⟨hfr, by omega⟩⟩

variable (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
  (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
include hA hC

/-- **The corners.** At `A` and `C` one tile, with its `α`; at `B` one `α` and three `β`. -/
theorem corner_counts120 :
    (angleCount D (D.target.pts 0) (tileα D) = 1 ∧ angleCount D (D.target.pts 0) (tileβ D) = 0 ∧
      angleCount D (D.target.pts 0) (tileγ D) = 0) ∧
    (angleCount D (D.target.pts 2) (tileα D) = 1 ∧ angleCount D (D.target.pts 2) (tileβ D) = 0 ∧
      angleCount D (D.target.pts 2) (tileγ D) = 0) ∧
    (angleCount D (D.target.pts 1) (tileα D) = 1 ∧ angleCount D (D.target.pts 1) (tileβ D) = 3 ∧
      angleCount D (D.target.pts 1) (tileγ D) = 0) := by
  have hTsum := cornerAngle_sum D.target
  have eA : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D := hA
  have eC : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = tileα D := by
    rw [cornerAngle, angle_comm]; exact hC
  have h0 : D.target.localAngle (D.target.pts 0) = (1 : ℤ) * tileα D + (0 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = _
    push_cast; linarith
  have h1 : D.target.localAngle (D.target.pts 1) = (-2 : ℤ) * tileα D + (1 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
    push_cast; linarith
  have h2 : D.target.localAngle (D.target.pts 2) = (1 : ℤ) * tileα D + (0 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = _
    push_cast; linarith
  have r0 := vertex_relations120 D hγ hirr _ 1 0 h0
  have r1 := vertex_relations120 D hγ hirr _ (-2) 1 h1
  have r2 := vertex_relations120 D hγ hirr _ 1 0 h2
  refine ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega⟩, ?_⟩
  have : angleCount D (D.target.pts 1) (tileβ D) ≤ 3 := by omega
  interval_cases h : angleCount D (D.target.pts 1) (tileβ D) <;> omega

end TriangleTiling
