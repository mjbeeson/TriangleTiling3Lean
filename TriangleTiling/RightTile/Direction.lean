/-
Directions of segments as complex numbers (for the direction classes of `theorem:isosceles2`).

A nonzero vector `v = (v₀, v₁)` of the plane is the complex number `z = v₀ + i v₁`, and its
direction up to sign is `dirC v = z / z̄` (a unit complex number, `e^{2iφ}` when `v` has angle
`φ`). Parallel vectors have the same `dirC`; perpendicular ones have opposite `dirC`; if the angle
between `u` and `v` is `φ`, then `dirC v = e^{±2iφ} dirC u`.
-/
import TriangleTiling.RightTile.DirClass
import Erdos634.Dissection

namespace TriangleTiling

open Erdos634.Geometry Complex ComplexConjugate

/-- The plane as the complex numbers. -/
def toC (v : Plane) : ℂ := ⟨v 0, v 1⟩

@[simp] theorem toC_re (v : Plane) : (toC v).re = v 0 := rfl
@[simp] theorem toC_im (v : Plane) : (toC v).im = v 1 := rfl

theorem toC_ne {v : Plane} (hv : v ≠ 0) : toC v ≠ 0 := by
  intro h
  apply hv
  have h0 : v 0 = 0 := by simpa using congrArg Complex.re h
  have h1 : v 1 = 0 := by simpa using congrArg Complex.im h
  ext i; fin_cases i <;> simp [h0, h1]

theorem conj_toC_ne {v : Plane} (hv : v ≠ 0) : conj (toC v) ≠ 0 :=
  (map_ne_zero _).mpr (toC_ne hv)

/-- The direction of `v` up to sign: `z / z̄`. -/
noncomputable def dirC (v : Plane) : ℂ := toC v / conj (toC v)

theorem dirC_ne {v : Plane} (hv : v ≠ 0) : dirC v ≠ 0 :=
  div_ne_zero (toC_ne hv) (conj_toC_ne hv)

theorem inner_coords (u v : Plane) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

theorem norm_sq_coords (u : Plane) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coords]; ring

theorem dirC_neg (v : Plane) : dirC (-v) = dirC v := by
  unfold dirC toC
  by_cases h : (⟨v 0, v 1⟩ : ℂ) = 0
  · have h' : (⟨(-v) 0, (-v) 1⟩ : ℂ) = 0 := by
      have h0 := congrArg Complex.re h; have h1 := congrArg Complex.im h
      simp at h0 h1; apply Complex.ext <;> simp [h0, h1]
    rw [h, h']
  · have hc : conj (⟨v 0, v 1⟩ : ℂ) ≠ 0 := (map_ne_zero _).mpr h
    have e : (⟨(-v) 0, (-v) 1⟩ : ℂ) = -⟨v 0, v 1⟩ := by apply Complex.ext <;> simp
    rw [e, map_neg, neg_div_neg_eq]

/-- **Parallel vectors** (`cross u v = 0`) have the same direction. -/
theorem dirC_of_cross {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) (h : cross u v = 0) :
    dirC v = dirC u := by
  unfold dirC
  rw [div_eq_div_iff (conj_toC_ne hv) (conj_toC_ne hu)]
  simp only [cross] at h
  apply Complex.ext <;> simp <;> linarith

/-- **Perpendicular vectors** have opposite directions. -/
theorem dirC_of_inner {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) (h : inner ℝ u v = 0) :
    dirC v = -dirC u := by
  unfold dirC
  rw [← neg_div, div_eq_div_iff (conj_toC_ne hv) (conj_toC_ne hu)]
  rw [inner_coords] at h
  apply Complex.ext <;> simp <;> linarith

/-- **Vectors at angle `φ`**: `dirC v = e^{±2iφ} dirC u`. -/
theorem dirC_of_angle {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) :
    dirC v = Complex.exp (2 * InnerProductGeometry.angle u v * Complex.I) * dirC u ∨
      dirC v = Complex.exp (-(2 * InnerProductGeometry.angle u v) * Complex.I) * dirC u := by
  set φ := InnerProductGeometry.angle u v
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hcos : inner ℝ u v = ‖u‖ * ‖v‖ * Real.cos φ := by
    rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm]; ring
  have hsin0 : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi
    (InnerProductGeometry.angle_nonneg u v) (InnerProductGeometry.angle_le_pi u v)
  -- Lagrange: `inner² + cross² = ‖u‖² ‖v‖²`, so `cross = ± ‖u‖ ‖v‖ sin φ`.
  have hlag : inner ℝ u v ^ 2 + cross u v ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [inner_coords, norm_sq_coords, norm_sq_coords]; simp only [cross]; ring
  have hcr : cross u v = ‖u‖ * ‖v‖ * Real.sin φ ∨ cross u v = -(‖u‖ * ‖v‖ * Real.sin φ) := by
    have : cross u v ^ 2 = (‖u‖ * ‖v‖ * Real.sin φ) ^ 2 := by
      have := Real.sin_sq_add_cos_sq φ
      rw [hcos] at hlag
      linear_combination hlag - (‖u‖ ^ 2 * ‖v‖ ^ 2) * this
    exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  -- `toC v · conj (toC u) = inner + i cross = r e^{±iφ}`.
  have hw : toC v * conj (toC u) = (inner ℝ u v : ℂ) + (cross u v : ℂ) * Complex.I := by
    rw [inner_coords]; simp only [cross]; apply Complex.ext <;> simp <;> ring
  have key : ∀ ψ : ℝ, cross u v = ‖u‖ * ‖v‖ * Real.sin ψ → Real.cos ψ = Real.cos φ →
      dirC v = Complex.exp (2 * ψ * Complex.I) * dirC u := by
    intro ψ hs hc
    have hw' : toC v * conj (toC u) = ((‖u‖ * ‖v‖ : ℝ) : ℂ) * Complex.exp (ψ * Complex.I) := by
      rw [hw, hcos, hs, ← hc, Complex.exp_mul_I]
      push_cast; ring
    have hwc : conj (toC v) * toC u = ((‖u‖ * ‖v‖ : ℝ) : ℂ) * Complex.exp (-(ψ * Complex.I)) := by
      have := congrArg conj hw'
      simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at this
      rw [this]; congr 1; rw [← Complex.exp_conj]; congr 1; simp
    have hr : ((‖u‖ * ‖v‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mul_pos hnu hnv).ne'
    unfold dirC
    rw [div_eq_iff (conj_toC_ne hv)]
    have e2 : Complex.exp (2 * ψ * Complex.I) =
        Complex.exp (ψ * Complex.I) / Complex.exp (-(ψ * Complex.I)) := by
      rw [← Complex.exp_sub]; ring_nf
    rw [e2]
    field_simp [conj_toC_ne hu, Complex.exp_ne_zero]
    linear_combination Complex.exp (-(ψ * Complex.I)) * hw' - Complex.exp (ψ * Complex.I) * hwc
  rcases hcr with h | h
  · exact Or.inl (key φ h rfl)
  · right
    have := key (-φ) (by rw [Real.sin_neg]; linarith) (Real.cos_neg φ)
    rw [this]; push_cast; ring_nf

end TriangleTiling
