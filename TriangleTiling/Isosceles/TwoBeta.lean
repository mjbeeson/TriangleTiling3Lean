/-
"Stars and centers", from Section 10 of M. Beeson, *Tilings of an isosceles triangle*.

Lean names follow the TeX labels: `lemma:twobeta` is `twobeta`.

The angle a tile presents at a point is Bonfioli's `Tri.localAngle`: the corner angle if the
point is a vertex of the tile, `2π` inside the tile, `π` inside an edge, `0` outside. Since `β`
is none of `0, π, 2π` (when `α ∉ ℚπ`), "tile `i` has its `β` angle at `P`" is exactly
`(D.tile i).localAngle P = β`.

Conventions as in `TriangleTiling.Isosceles.AreaEquation`: target `ABC = target.pts 0, 1, 2`
with base `AC`; model tile with angles `α, β, γ` at `model.pts 0, 1, 2`.
-/
import Erdos634.PinPlumbing

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-- Every tile's local angle at any point is one of `α, β, γ, π, 2π, 0`, where `α, β, γ` are
the corner angles of the model tile. -/
theorem localAngle_mem {N : ℕ} (D : CongruentDissection N) (v : Plane) (i : Fin N) :
    (D.tile i).localAngle v = cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) ∨
    (D.tile i).localAngle v = cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) ∨
    (D.tile i).localAngle v = cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) ∨
    (D.tile i).localAngle v = Real.pi ∨ (D.tile i).localAngle v = 2 * Real.pi ∨
    (D.tile i).localAngle v = 0 := by
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) v with ⟨j, -, hval⟩ | h | h | h
  · obtain ⟨k, hk⟩ := congruent_corner_angles (D.tiles_congruent i).symm j
    rw [hval, hk]
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- A sum of terms, each one of five distinct nonzero values `v₀, …, v₄` or `0`, is the sum of
the values weighted by how often each occurs. -/
theorem sum_eq_counts {ι : Type*} [Fintype ι] [DecidableEq ℝ] (f : ι → ℝ) (v : Fin 5 → ℝ)
    (hv0 : ∀ j, v j ≠ 0) (hinj : Function.Injective v)
    (hf : ∀ i, (∃ j, f i = v j) ∨ f i = 0) :
    ∑ i, f i = ∑ j, ((Finset.univ.filter fun i => f i = v j).card : ℝ) * v j := by
  have hpt : ∀ i, f i = ∑ j, if f i = v j then v j else 0 := by
    intro i
    rcases hf i with ⟨j, hj⟩ | h0
    · rw [Finset.sum_eq_single j]
      · simp [hj]
      · intro k _ hkj
        rw [if_neg]
        rw [hj]; exact fun h => hkj (hinj h).symm
      · simp
    · rw [h0, Finset.sum_eq_zero]
      intro k _
      rw [if_neg (fun h => hv0 k h.symm)]
  rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- The vertex-figure arithmetic of `lemma:twobeta`. With `γ = 2α`, `β = π - 3α` and
`α ∉ ℚπ`, if `x α + y β + z γ + u π + w (2π) = s α + t π` with `t ∈ {0, 1}`, then
`y ≤ 1` and `z ≤ 1`. The three cases of the lemma are `(s, t) = (0, 1)` (a point inside a
side, angle sum `π`), `(1, 0)` (the corners `A`, `C`, angle `α`) and `(-2, 1)` (the apex `B`,
angle `π - 2α`). -/
theorem twobeta_arith {α : ℝ} (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (x y z u w : ℕ) (s t : ℤ) (hst : (t = 1 ∧ s ≤ 0) ∨ (t = 0 ∧ s = 1))
    (h : (x : ℝ) * α + y * (Real.pi - 3 * α) + z * (2 * α) + u * Real.pi + w * (2 * Real.pi)
      = s * α + t * Real.pi) :
    y ≤ 1 ∧ z ≤ 1 := by
  have key : (((x : ℤ) - 3 * y + 2 * z - s : ℤ) : ℝ) * α
      + (((y : ℤ) + u + 2 * w - t : ℤ) : ℝ) * Real.pi = 0 := by
    push_cast; linear_combination h
  obtain ⟨h1, h2⟩ := angle_indep hirr _ _ key
  omega

/-- **Lemma `lemma:twobeta`.** Let the isosceles triangle `ABC` with base angles `α` (at `A`
and `C`) be `N`-tiled by a tile with angles `(α, β, 2α)`, where `α` is not a rational multiple
of `π`. Let `P` be a point on the boundary of `ABC`. Then there are not two `β` angles of tiles
at `P`, and there are not two `γ` angles of tiles at `P`.

The paper also assumes that the tile is not a right triangle; the proof does not use it. The
proof is the paper's: the angles at `P` sum to `π` (inside a side), `α` (at `A` or `C`) or
`π - 2α` (at `B`), and since `α ∉ ℚπ` the only integer relation among `α, β, γ, π` is
`3α + β = π` (with `γ = 2α`). -/
theorem twobeta {N : ℕ} (D : CongruentDissection N)
    (hγ : ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) =
      2 * ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hirr : ¬ ∃ r : ℚ, ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    {P : Plane} (hP : P ∈ frontier D.target.carrier) :
    (Finset.univ.filter fun i =>
        (D.tile i).localAngle P = ∠ (D.model.pts 2) (D.model.pts 1) (D.model.pts 0)).card ≤ 1 ∧
    (Finset.univ.filter fun i =>
        (D.tile i).localAngle P = ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1)).card ≤ 1 := by
  classical
  set α := ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) with hαdef
  set β := ∠ (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) with hβdef
  set γ := ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) with hγdef
  -- The tile's angles: `α + β + γ = π`, so `β = π - 3α`.
  have hsum3 : α + β + γ = Real.pi := cornerAngle_sum D.model
  have hβ : β = Real.pi - 3 * α := by linarith
  -- `α, β, γ, π, 2π` are distinct and nonzero, because `α ∉ ℚπ`.
  have hne : ∀ p q : ℤ, p ≠ 0 → (p : ℝ) * α ≠ q * Real.pi := by
    intro p q hp h
    exact hp (angle_indep hirr p (-q) (by push_cast; linarith)).1
  have hpi := Real.pi_pos
  let v : Fin 5 → ℝ := ![α, β, γ, Real.pi, 2 * Real.pi]
  have hv0 : ∀ j, v j ≠ 0 := by
    intro j; fin_cases j
    · exact fun h => hne 1 0 one_ne_zero (by simp [v] at h ⊢; linarith)
    · exact fun h => hne 3 1 (by norm_num) (by simp [v] at h; push_cast; linarith)
    · exact fun h => hne 1 0 one_ne_zero (by simp [v] at h; push_cast; linarith)
    · simp [v, hpi.ne']
    · simp [v, hpi.ne']
  have hinj : Function.Injective v := by
    intro j k hjk
    fin_cases j <;> fin_cases k <;> simp [v] at hjk ⊢
    all_goals first
      | exact hne 4 1 (by norm_num) (by push_cast; linarith)
      | exact hne 1 0 one_ne_zero (by push_cast; linarith)
      | exact hne 1 1 one_ne_zero (by push_cast; linarith)
      | exact hne 1 2 one_ne_zero (by push_cast; linarith)
      | exact hne 5 1 (by norm_num) (by push_cast; linarith)
      | exact hne 3 (-1) (by norm_num) (by push_cast; linarith)
      | exact hne 2 1 (by norm_num) (by push_cast; linarith)
  have hf : ∀ i, (∃ j, (D.tile i).localAngle P = v j) ∨ (D.tile i).localAngle P = 0 := by
    intro i
    rcases localAngle_mem D P i with h | h | h | h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · exact Or.inl ⟨2, h⟩
    · exact Or.inl ⟨3, h⟩
    · exact Or.inl ⟨4, h⟩
    · exact Or.inr h
  have hcount := sum_eq_counts (fun i => (D.tile i).localAngle P) v hv0 hinj hf
  rw [D.toDissection.sum_localAngle_eq P, Fin.sum_univ_five] at hcount
  set c := fun j => (Finset.univ.filter fun i => (D.tile i).localAngle P = v j).card with hc
  -- The local angle of the target at `P`: `α` at `A` or `C`, `π - 2α` at `B`, `π` elsewhere.
  have htarget : ∃ s t : ℤ, ((t = 1 ∧ s ≤ 0) ∨ (t = 0 ∧ s = 1)) ∧
      D.target.localAngle P = s * α + t * Real.pi := by
    by_cases hv : P ∈ Set.range D.target.pts
    · obtain ⟨k, rfl⟩ := hv
      rw [Tri.localAngle_vertex]
      have hT := cornerAngle_sum D.target
      have eA : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = α := hA
      have eC : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = α := by
        rw [cornerAngle, angle_comm]; exact hC
      fin_cases k
      · refine ⟨1, 0, Or.inr ⟨rfl, rfl⟩, ?_⟩
        show cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = _
        push_cast; linarith
      · refine ⟨-2, 1, Or.inl ⟨rfl, by norm_num⟩, ?_⟩
        show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
        push_cast; linarith
      · refine ⟨1, 0, Or.inr ⟨rfl, rfl⟩, ?_⟩
        show cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = _
        push_cast; linarith
    · exact ⟨0, 1, Or.inl ⟨rfl, le_rfl⟩, by
        rw [D.target.localAngle_frontier hP hv]; push_cast; ring⟩
  obtain ⟨s, t, hst, ht⟩ := htarget
  rw [ht] at hcount
  have hcount' : (s : ℝ) * α + t * Real.pi = (c 0 : ℝ) * α + (c 1 : ℝ) * β + (c 2 : ℝ) * γ
      + (c 3 : ℝ) * Real.pi + (c 4 : ℝ) * (2 * Real.pi) := hcount
  exact twobeta_arith hirr (c 0) (c 1) (c 2) (c 3) (c 4) s t hst (by
    rw [← hβ, ← (show γ = 2 * α from hγ)]
    linarith)

end TriangleTiling
