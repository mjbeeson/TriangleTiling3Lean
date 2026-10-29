/-
`lemma:cminusb` of M. Beeson, *Triangle tiling: the case 3α + 2β = π* (arXiv 1206.2229v4).
Statement not yet checked by Beeson; in the style of `lemma:anglesOK` (the triangle `ABC` with
`a = |BC|`, `b = |CA|`, `c = |AB|` opposite `A, B, C`).
-/
import TriangleTiling.ThreeAlpha.Basic

namespace TriangleTiling.ThreeAlpha

open EuclideanGeometry Real

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Lemma `lemma:cminusb`.** Suppose `3α + 2β = π` and `T` is a triangle with angles
`(α, β, γ)` and sides `(a, b, c)`. Then `c - b` is not an integer multiple of `a`. -/
theorem cminusb {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (hrel : 3 * ∠ B A C + 2 * ∠ A B C = π) :
    ¬ ∃ n : ℤ, dist A B - dist C A = n * dist B C := by
  rintro ⟨n, hn⟩
  have hBC : B ≠ C := fun h => absurd (hABC.injective (show ![A, B, C] 1 = ![A, B, C] 2 from h))
    (by decide)
  have hAB : A ≠ B := fun h => absurd (hABC.injective (show ![A, B, C] 0 = ![A, B, C] 1 from h))
    (by decide)
  have ha : 0 < dist B C := dist_pos.mpr hBC
  have hc : 0 < dist A B := dist_pos.mpr hAB
  have hb := (anglesOK hABC).mp hrel
  obtain ⟨-, hs, -⟩ := singamma hABC hrel
  -- `c - b = a²/c`, so `n = a/c = 2 sin (α/2) ∈ (0, 1)`.
  rw [hb] at hn
  have hn' : (n : ℝ) = dist B C / dist A B := by
    field_simp at hn ⊢
    nlinarith [ha]
  rw [hs] at hn'
  have hpos : 0 < 2 * Real.sin (∠ B A C / 2) := by rw [← hs]; positivity
  have hlt : 2 * Real.sin (∠ B A C / 2) < 1 := by
    have h6 : ∠ B A C / 2 < π / 6 := by
      have : 0 < ∠ A B C :=
        angle_pos_of_not_collinear (affineIndependent_iff_not_collinear_set.mp hABC)
      linarith
    have := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [angle_nonneg B A C, Real.pi_pos]) (by linarith [Real.pi_pos]) h6
    rw [Real.sin_pi_div_six] at this
    linarith
  rw [← hn'] at hpos hlt
  have h1 : (0 : ℤ) < n := by exact_mod_cast hpos
  have h2 : n < 1 := by exact_mod_cast hlt
  omega

end TriangleTiling.ThreeAlpha
