/-
`lemma:shapeareas` of M. Beeson, *Triangle tiling: the case 3α + 2β = π* (arXiv 1206.2229v4):
the number of tiles in terms of `Λ` for the five shapes.
-/
import TriangleTiling.ThreeAlpha.Defs
import TriangleTiling.ThreeAlpha.Basic
import TriangleTiling.Isosceles.AreaEquation
import Erdos634.TriLawSin
import Erdos634.Draft.FluxCRow12

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry


/-! ### Law of sines and area for a `Tri` -/

theorem tri_angle_lt_pi (T : Tri) (k : Fin 3) : T.angleAt k < Real.pi := by
  have hs := T.angleAt_sum
  have h0 := T.angleAt_pos' 0
  have h1 := T.angleAt_pos' 1
  have h2 := T.angleAt_pos' 2
  fin_cases k <;> simp <;> linarith

theorem tri_sin_pos (T : Tri) (k : Fin 3) : 0 < Real.sin (T.angleAt k) :=
  Real.sin_pos_of_pos_of_lt_pi (T.angleAt_pos' k) (tri_angle_lt_pi T k)

theorem circumdiam_pos (T : Tri) : 0 < circumdiam T :=
  div_pos (T.oppLen_pos 0) (tri_sin_pos T 0)

/-- **Law of sines**: each side is the circumdiameter times the sine of the opposite angle. -/
theorem lawsin (T : Tri) (k : Fin 3) : T.oppLen k = circumdiam T * Real.sin (T.angleAt k) := by
  have hs0 := (tri_sin_pos T 0).ne'
  unfold circumdiam
  rw [div_mul_eq_mul_div, eq_div_iff hs0]
  have l0 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 0
  have l2 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 2
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · ring
  · change Real.sin (T.angleAt 1) * T.oppLen 0 = Real.sin (T.angleAt 0) * T.oppLen 1 at l0
    linarith
  · change Real.sin (T.angleAt 0) * T.oppLen 2 = Real.sin (T.angleAt 2) * T.oppLen 0 at l2
    linarith

/-- Heron in sine form: `16 (area)² = 4 (|CA| |AB| sin A)²`. -/
theorem heron_sin (T : Tri) :
    heron16 (T.oppLen 0) (T.oppLen 1) (T.oppLen 2)
      = 4 * (T.oppLen 1 * T.oppLen 2 * Real.sin (T.angleAt 0)) ^ 2 := by
  have lc := EuclideanGeometry.law_cos (T.pts 1) (T.pts 0) (T.pts 2)
  have e0 : T.oppLen 0 = dist (T.pts 1) (T.pts 2) := rfl
  have e1 : T.oppLen 1 = dist (T.pts 2) (T.pts 0) := rfl
  have e2 : T.oppLen 2 = dist (T.pts 0) (T.pts 1) := rfl
  have ea : T.angleAt 0 = EuclideanGeometry.angle (T.pts 1) (T.pts 0) (T.pts 2) := rfl
  rw [dist_comm (T.pts 1) (T.pts 0), dist_comm (T.pts 2) (T.pts 0)] at lc
  rw [e0, e1, e2, ea, dist_comm (T.pts 2) (T.pts 0)]
  have hsc := Real.sin_sq_add_cos_sq (EuclideanGeometry.angle (T.pts 1) (T.pts 0) (T.pts 2))
  unfold heron16
  have hx : dist (T.pts 1) (T.pts 2) ^ 2 = dist (T.pts 0) (T.pts 1) ^ 2 + dist (T.pts 0) (T.pts 2) ^ 2
      - 2 * dist (T.pts 0) (T.pts 1) * dist (T.pts 0) (T.pts 2)
        * Real.cos (EuclideanGeometry.angle (T.pts 1) (T.pts 0) (T.pts 2)) := by nlinarith [lc]
  rw [show dist (T.pts 1) (T.pts 2) ^ 4 = (dist (T.pts 1) (T.pts 2) ^ 2) ^ 2 by ring, hx]
  linear_combination (-4 * dist (T.pts 0) (T.pts 1) ^ 2 * dist (T.pts 0) (T.pts 2) ^ 2) * hsc

/-- **Area in sines**: `N d_T² sin α sin β sin γ = d_{ABC}² sin A sin B sin C`. -/
theorem area_sines {N : ℕ} (D : CongruentDissection N) :
    (N : ℝ) * (circumdiam D.model ^ 2 * (Real.sin (D.model.angleAt 0) *
        Real.sin (D.model.angleAt 1) * Real.sin (D.model.angleAt 2)))
      = circumdiam D.target ^ 2 * (Real.sin (D.target.angleAt 0) *
        Real.sin (D.target.angleAt 1) * Real.sin (D.target.angleAt 2)) := by
  have h := area_heron D
  change (N : ℝ) ^ 2 * heron16 (D.model.oppLen 0) (D.model.oppLen 1) (D.model.oppLen 2)
    = heron16 (D.target.oppLen 0) (D.target.oppLen 1) (D.target.oppLen 2) at h
  rw [heron_sin, heron_sin] at h
  have key : ∀ T : Tri, T.oppLen 1 * T.oppLen 2 * Real.sin (T.angleAt 0)
      = circumdiam T ^ 2 * (Real.sin (T.angleAt 0) * Real.sin (T.angleAt 1) *
        Real.sin (T.angleAt 2)) := by
    intro T; rw [lawsin T 1, lawsin T 2]; ring
  rw [key, key] at h
  have p1 : 0 < circumdiam D.model ^ 2 * (Real.sin (D.model.angleAt 0) *
      Real.sin (D.model.angleAt 1) * Real.sin (D.model.angleAt 2)) := by
    have := circumdiam_pos D.model
    have := tri_sin_pos D.model 0; have := tri_sin_pos D.model 1; have := tri_sin_pos D.model 2
    positivity
  have p2 : 0 < circumdiam D.target ^ 2 * (Real.sin (D.target.angleAt 0) *
      Real.sin (D.target.angleAt 1) * Real.sin (D.target.angleAt 2)) := by
    have := circumdiam_pos D.target
    have := tri_sin_pos D.target 0; have := tri_sin_pos D.target 1; have := tri_sin_pos D.target 2
    positivity
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set X := circumdiam D.model ^ 2 * (Real.sin (D.model.angleAt 0) *
      Real.sin (D.model.angleAt 1) * Real.sin (D.model.angleAt 2))
  set Y := circumdiam D.target ^ 2 * (Real.sin (D.target.angleAt 0) *
      Real.sin (D.target.angleAt 1) * Real.sin (D.target.angleAt 2))
  have h' : ((N : ℝ) * X) ^ 2 = Y ^ 2 := by linear_combination h / 4
  exact (sq_eq_sq₀ (by positivity) p2.le).mp h'


/-- The tile in the coordinates of `lemma:deltacoords`: with `δ = α + β`, `s = 2 cos δ`,
`a = s c`, `b = (1 - s²) c`, `0 < s < 1`, the circumdiameter is `c / sin δ`, and the sines of
the tile's angles are `s sin δ`, `(1 - s²) sin δ`, `sin δ`. -/
theorem model_facts {N : ℕ} (D : CongruentDissection N) {α β γ a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (hT : TileSides D α β γ a b c) :
    0 < α ∧ 0 < β ∧ γ = 2 * α + β ∧ 0 < Real.sin (α + β) ∧ 0 < c ∧
      a = 2 * Real.cos (α + β) * c ∧ b = (1 - (2 * Real.cos (α + β)) ^ 2) * c ∧
      0 < 2 * Real.cos (α + β) ∧ 2 * Real.cos (α + β) < 1 ∧
      circumdiam D.model = c / Real.sin (α + β) ∧
      Real.sin (D.model.angleAt 0) * Real.sin (D.model.angleAt 1) * Real.sin (D.model.angleAt 2)
        = Real.sin α * Real.sin β * Real.sin (2 * α + β) := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  have hα : 0 < α := h0 ▸ D.model.angleAt_pos' _
  have hβ : 0 < β := h1 ▸ D.model.angleAt_pos' _
  have hsum : D.model.angleAt (σ 0) + D.model.angleAt (σ 1) + D.model.angleAt (σ 2) = Real.pi := by
    have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    simp only [Fin.sum_univ_three] at e
    rw [e, D.model.angleAt_sum]
  have hγ : γ = 2 * α + β := by rw [h0, h1, h2] at hsum; linarith
  have hπ := Real.pi_pos
  have hS : 0 < Real.sin (α + β) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hSγ : Real.sin γ = Real.sin (α + β) := by
    rw [hγ, show 2 * α + β = Real.pi - (α + β) by linarith, Real.sin_pi_sub]
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨r1, r2, -, -, -, -, -, -⟩ := r
  rw [div_eq_iff hS.ne'] at r1 r2
  have hd := circumdiam_pos D.model
  have la := lawsin D.model (σ 0)
  have lb := lawsin D.model (σ 1)
  have lc := lawsin D.model (σ 2)
  rw [l0, h0] at la
  rw [l1, h1] at lb
  rw [l2, h2, hSγ] at lc
  have hc : 0 < c := by rw [lc]; positivity
  have hdc : circumdiam D.model = c / Real.sin (α + β) := by rw [lc]; field_simp
  have hcos : 0 < Real.cos (α + β) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcos2 : Real.cos (α + β) < 1 / 2 := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  refine ⟨hα, hβ, hγ, hS, hc, ?_, ?_, by linarith, by linarith, hdc, ?_⟩
  · rw [la, r1, lc]; ring
  · rw [lb, r2, lc]; ring
  · have e := Equiv.prod_comp σ (fun k => Real.sin (D.model.angleAt k))
    simp only [Fin.prod_univ_three] at e
    rw [← e, h0, h1, h2, hγ]

/-- **Lemma `lemma:shapeareas`.** Let `ABC` be tiled by `N` copies of the tile `T`
(`3α + 2β = π`, `s = a/c`). Then, with the angles of `ABC` listed at `A`, `B`, `C`:

| angles of `ABC` | `N/Λ²` |
|---|---|
| `(2α, β, α + β)` | `2 - s²` |
| `(β, 3α, β)` | `(1 - s²)²(3 - s²)` |
| `(α + β, α, α + β)` | `1/(1 - s²)` |
| `(α, α + 2β, α)` | `s²(2 - s²)/(1 - s²)` |
| `(2α, α, 2β)` | `s²(2 - s²)(3 - s²)` | -/
theorem shapeareas {N : ℕ} (D : CongruentDissection N) {α β γ a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (hT : TileSides D α β γ a b c) :
    let s := a / c
    let Λ := Lam D
    let shape := fun x y z : ℝ =>
      D.target.angleAt 0 = x ∧ D.target.angleAt 1 = y ∧ D.target.angleAt 2 = z
    (shape (2 * α) β (α + β) → N / Λ ^ 2 = 2 - s ^ 2) ∧
    (shape β (3 * α) β → N / Λ ^ 2 = (1 - s ^ 2) ^ 2 * (3 - s ^ 2)) ∧
    (shape (α + β) α (α + β) → N / Λ ^ 2 = 1 / (1 - s ^ 2)) ∧
    (shape α (α + 2 * β) α → N / Λ ^ 2 = s ^ 2 * (2 - s ^ 2) / (1 - s ^ 2)) ∧
    (shape (2 * α) α (2 * β) → N / Λ ^ 2 = s ^ 2 * (2 - s ^ 2) * (3 - s ^ 2)) := by
  intro s Λ shape
  obtain ⟨hα, hβ, hγ, hS, hc, ha, hb, hs0, hs1, hdm, hPm⟩ := model_facts D hrel hT
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := r
  rw [div_eq_iff hS.ne'] at r1 r2 r3 r4 r5 r6 r7 r8
  set S := Real.sin (α + β)
  set t := 2 * Real.cos (α + β)
  have hst : s = t := by simp only [s]; rw [ha]; field_simp
  have hA := area_sines D
  have hdt := circumdiam_pos D.target
  have hdm' := circumdiam_pos D.model
  have hΛ : Λ = circumdiam D.target / circumdiam D.model := rfl
  have hNΛ : (N : ℝ) / Λ ^ 2 = (Real.sin (D.target.angleAt 0) * Real.sin (D.target.angleAt 1) *
      Real.sin (D.target.angleAt 2)) / (Real.sin α * Real.sin β * Real.sin (2 * α + β)) := by
    rw [← hPm, hΛ, div_pow, div_div_eq_mul_div, eq_div_iff (by
      have := tri_sin_pos D.model 0; have := tri_sin_pos D.model 1; have := tri_sin_pos D.model 2
      positivity), div_mul_eq_mul_div, div_eq_iff (by positivity)]
    linarith [hA]
  have ht1 : 1 - t ^ 2 ≠ 0 := by nlinarith
  have hPm' : Real.sin α * Real.sin β * Real.sin (2 * α + β) = t * (1 - t ^ 2) * S ^ 3 := by
    rw [r1, r2, r3]; ring
  rw [hst]
  refine ⟨fun ⟨e0, e1, e2⟩ => ?_, fun ⟨e0, e1, e2⟩ => ?_, fun ⟨e0, e1, e2⟩ => ?_,
    fun ⟨e0, e1, e2⟩ => ?_, fun ⟨e0, e1, e2⟩ => ?_⟩ <;>
    rw [hNΛ, hPm', e0, e1, e2]
  · rw [r5, r2]; first | (field_simp; ring) | field_simp
  · rw [r2, r7]; first | (field_simp; ring) | field_simp
  · rw [r1]; first | (field_simp; ring) | field_simp
  · rw [r1, r6]; first | (field_simp; ring) | field_simp
  · rw [r5, r1, r8]; first | (field_simp; ring) | field_simp

end TriangleTiling.ThreeAlpha
