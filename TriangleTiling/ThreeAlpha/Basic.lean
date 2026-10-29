/-
Lemmas from Section 2 ("Some basic lemmas") of M. Beeson, *Triangle tiling: the case
3α + 2β = π* (arXiv 1206.2229v4), and `lemma:primeimpliesjone` from its Section 9.

Lean names follow the TeX labels: `lemma:singamma` is `singamma`, `lemma:anglesOK` is
`anglesOK`, and so on.

A triangle `ABC` is the tile: `α = ∠BAC`, `β = ∠ABC`, `γ = ∠ACB`, with opposite sides
`a = |BC|`, `b = |CA|`, `c = |AB|` (the paper's Convention 1), and `s = 2 sin (α/2)`.
-/
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace TriangleTiling.ThreeAlpha

open EuclideanGeometry Real

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The facts about a nondegenerate triangle used below: positive sides and angles, the angle
sum, and the laws of sines and cosines in the form needed. -/
private theorem tri_facts {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) :
    0 < dist B C ∧ 0 < dist C A ∧ 0 < dist A B ∧
      0 < ∠ B A C ∧ 0 < ∠ A B C ∧ 0 < ∠ A C B ∧ ∠ B A C + ∠ A B C + ∠ A C B = π ∧
      sin (∠ A C B) * dist B C = sin (∠ B A C) * dist A B ∧
      sin (∠ A B C) * dist A B = sin (∠ A C B) * dist C A ∧
      dist B C ^ 2 = dist A B ^ 2 + dist C A ^ 2 - 2 * dist A B * dist C A * cos (∠ B A C) ∧
      dist C A ^ 2 = dist A B ^ 2 + dist B C ^ 2 - 2 * dist A B * dist B C * cos (∠ A B C) := by
  have h := affineIndependent_iff_not_collinear_set.mp hABC
  have h1 : ¬ Collinear ℝ ({B, A, C} : Set P) := by rwa [Set.insert_comm]
  have h2 : ¬ Collinear ℝ ({A, C, B} : Set P) := by rwa [Set.pair_comm]
  have hAB : A ≠ B := ne₁₂_of_not_collinear h
  have hAC : A ≠ C := ne₁₃_of_not_collinear h
  have hBC : B ≠ C := ne₂₃_of_not_collinear h
  have hsum := angle_add_angle_add_angle_eq_pi B hAC.symm
  rw [angle_comm C B A] at hsum
  have ls1 := law_sin A C B
  have ls2 := law_sin C B A
  have lc1 := law_cos B A C
  have lc2 := law_cos A B C
  rw [angle_comm C B A] at ls2
  simp only [dist_comm B A, dist_comm A C, dist_comm C B] at ls1 ls2 lc1 lc2
  refine ⟨dist_pos.mpr hBC, dist_pos.mpr hAC.symm, dist_pos.mpr hAB, angle_pos_of_not_collinear h1,
    angle_pos_of_not_collinear h, angle_pos_of_not_collinear h2, by linarith, by linarith,
    by linarith, by nlinarith [lc1], by nlinarith [lc2]⟩

/-- **Lemma `lemma:singamma`.** If the angles `(α, β, γ)` of `ABC` satisfy `3α + 2β = π`,
then `sin γ = cos (α/2)`, `a/c = s` and `b/c = 1 - s²`, where `s = 2 sin (α/2)`. -/
theorem singamma {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (hrel : 3 * ∠ B A C + 2 * ∠ A B C = π) :
    sin (∠ A C B) = cos (∠ B A C / 2) ∧
      dist B C / dist A B = 2 * sin (∠ B A C / 2) ∧
      dist C A / dist A B = 1 - (2 * sin (∠ B A C / 2)) ^ 2 := by
  obtain ⟨ha, -, hc, hα, hβ, -, hsum, ls1, ls2, -, -⟩ := tri_facts hABC
  set x := ∠ B A C / 2 with hx
  have hxpos : 0 < x := by linarith
  have hxlt : x < π / 2 := by linarith
  have hcos : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith, hxlt⟩
  have hγ : ∠ A C B = x + π / 2 := by linarith
  have hβ' : ∠ A B C = π / 2 - 3 * x := by linarith
  have hα' : ∠ B A C = 2 * x := by linarith
  have hsγ : sin (∠ A C B) = cos x := by rw [hγ, sin_add_pi_div_two]
  rw [hsγ, hα', sin_two_mul] at ls1
  rw [hsγ, hβ', sin_pi_div_two_sub, cos_three_mul] at ls2
  have hsc := sin_sq_add_cos_sq x
  refine ⟨hsγ, ?_, ?_⟩
  · rw [div_eq_iff hc.ne']
    have : cos x * (dist B C - 2 * sin x * dist A B) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  · rw [div_eq_iff hc.ne']
    have : cos x * (dist C A - (1 - (2 * sin x) ^ 2) * dist A B) = 0 := by
      linear_combination (-1) * ls2 + (4 * cos x * dist A B) * hsc
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith

/-- **Lemma `lemma:anglesOK`.** The angles of `ABC` satisfy `3α + 2β = π` if and only if
`b = c - a²/c`. -/
theorem anglesOK {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) :
    3 * ∠ B A C + 2 * ∠ A B C = π ↔ dist C A = dist A B - dist B C ^ 2 / dist A B := by
  obtain ⟨ha, hb, hc, hα, hβ, hγ, hsum, -, -, lc1, lc2⟩ := tri_facts hABC
  constructor
  · intro hrel
    obtain ⟨-, h1, h2⟩ := singamma hABC hrel
    rw [div_eq_iff hc.ne'] at h1 h2
    rw [h2, h1]
    field_simp
  · intro hb'
    set s := dist B C / dist A B with hs
    have ha' : dist B C = s * dist A B := by rw [hs, div_mul_cancel₀ _ hc.ne']
    have hb2 : dist C A = (1 - s ^ 2) * dist A B := by
      rw [hb', ha']; field_simp
    have hs0 : 0 < s := by positivity
    have hs1 : s ^ 2 < 1 := by
      by_contra hn
      have : (1 - s ^ 2) * dist A B ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hc.le
      linarith
    -- The law of cosines gives `cos α = 1 - s²/2` and `cos β = s(3 - s²)/2`.
    rw [ha', hb2] at lc1 lc2
    have hcα : cos (∠ B A C) = 1 - s ^ 2 / 2 := by
      have hpos : 0 < 2 * (1 - s ^ 2) * dist A B ^ 2 := by
        have : 0 < 1 - s ^ 2 := by linarith
        positivity
      have : 2 * (1 - s ^ 2) * dist A B ^ 2 * (cos (∠ B A C) - (1 - s ^ 2 / 2)) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    have hcβ : cos (∠ A B C) = s * (3 - s ^ 2) / 2 := by
      have hpos : 0 < 2 * s * dist A B ^ 2 := by positivity
      have : 2 * s * dist A B ^ 2 * (cos (∠ A B C) - s * (3 - s ^ 2) / 2) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    -- With `x = α/2`, `sin x = s/2`.
    set x := ∠ B A C / 2 with hx
    have hα' : ∠ B A C = 2 * x := by linarith
    have hxpos : 0 < x := by linarith
    have hsinx : sin x = s / 2 := by
      have hsin0 : 0 < sin x := sin_pos_of_pos_of_lt_pi hxpos (by linarith)
      rw [hα', cos_two_mul] at hcα
      have := sin_sq_add_cos_sq x
      have : (sin x - s / 2) * (sin x + s / 2) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    -- `α ≤ π/3`, since `cos α ≥ 1/2`.
    have hαle : ∠ B A C ≤ π / 3 := by
      by_contra hn
      have := cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (not_le.mp hn)
      rw [cos_pi_div_three, hcα] at this
      linarith
    -- `cos β = cos (π/2 - 3x)`, and both angles lie in `[0, π]`.
    have hcos : cos (∠ A B C) = cos (π / 2 - 3 * x) := by
      rw [cos_pi_div_two_sub, sin_three_mul, hsinx, hcβ]
      ring
    have := injOn_cos ⟨hβ.le, by linarith⟩ ⟨by linarith, by linarith⟩ hcos
    linarith

/-- **Lemma `lemma:gsquare`.** Suppose `3α + 2β = π` and `(a, b, c)` are the sides of a triangle
with angles `(α, β, γ)`. Suppose `(a, b, c)` are integers with no common factor, and let
`a/c = m/k` in lowest terms. Then `(a, b, c) = (mk, k² - m², k²)`, `k = gcd (a, c)`, `m = a/k`
and `m < k`. -/
theorem gsquare {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (hrel : 3 * ∠ B A C + 2 * ∠ A B C = π) {a b c m k : ℕ}
    (ha : dist B C = a) (hb : dist C A = b) (hc : dist A B = c)
    (hgcd : Nat.gcd (Nat.gcd a b) c = 1)
    (hmk : Nat.Coprime m k) (hk : 0 < k) (hratio : a * k = m * c) :
    a = m * k ∧ b = k ^ 2 - m ^ 2 ∧ c = k ^ 2 ∧ k = Nat.gcd a c ∧ m = a / k ∧ m < k := by
  have hb0 : 0 < b := by
    have := (tri_facts hABC).2.1
    rw [hb] at this
    exact_mod_cast this
  have hc0 : 0 < c := by
    have := (tri_facts hABC).2.2.1
    rw [hc] at this
    exact_mod_cast this
  -- By `lemma:anglesOK`, `a² + bc = c²`.
  have hrel' : a ^ 2 + b * c = c ^ 2 := by
    have h := (anglesOK hABC).mp hrel
    rw [ha, hb, hc] at h
    have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc0.ne'
    have : ((a ^ 2 + b * c : ℕ) : ℝ) = ((c ^ 2 : ℕ) : ℝ) := by
      push_cast
      rw [h]
      field_simp
      ring
    exact_mod_cast this
  -- `c = kt` and `a = mt`.
  obtain ⟨t, rfl⟩ : k ∣ c :=
    (Nat.Coprime.symm hmk).dvd_of_dvd_mul_left ⟨a, by rw [← hratio, mul_comm]⟩
  have hat : a = m * t := by
    apply Nat.eq_of_mul_eq_mul_left hk
    rw [mul_comm k a, hratio]
    ring
  subst hat
  have ht : 0 < t := Nat.pos_of_mul_pos_left hc0
  -- Cancelling `t`: `m²t + bk = k²t`.
  have h1 : m ^ 2 * t + b * k = k ^ 2 * t := by
    apply Nat.eq_of_mul_eq_mul_left ht
    linear_combination hrel'
  -- So `k ∣ m²t`, hence `k ∣ t`: `t = ku`.
  have hkt : k ∣ t := by
    have : k ∣ m ^ 2 * t := by
      have h2 : k ∣ m ^ 2 * t + b * k := by rw [h1]; exact ⟨k * t, by ring⟩
      exact (Nat.dvd_add_left (Dvd.intro_left b rfl)).mp h2
    exact (Nat.Coprime.pow_right 2 hmk.symm).dvd_of_dvd_mul_left this
  obtain ⟨u, rfl⟩ := hkt
  have h2 : m ^ 2 * u + b = k ^ 2 * u := by
    apply Nat.eq_of_mul_eq_mul_left hk
    linear_combination h1
  -- `u` divides `a`, `b` and `c`, so `u = 1`.
  have hu : u = 1 := by
    have hub : u ∣ b := by
      have : u ∣ m ^ 2 * u + b := by rw [h2]; exact Dvd.intro_left _ rfl
      exact (Nat.dvd_add_right (Dvd.intro_left _ rfl)).mp this
    have : u ∣ Nat.gcd (Nat.gcd (m * (k * u)) b) (k * (k * u)) :=
      Nat.dvd_gcd (Nat.dvd_gcd ⟨m * k, by ring⟩ hub) ⟨k * k, by ring⟩
    rw [hgcd] at this
    exact Nat.dvd_one.mp this
  subst hu
  simp only [mul_one] at h2 ⊢
  have hmk' : m < k := by
    have : m ^ 2 < k ^ 2 := by linarith
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp this
  refine ⟨trivial, by rw [← h2, Nat.add_sub_cancel_left], by ring, ?_, ?_, hmk'⟩
  · rw [Nat.gcd_mul_right, Nat.Coprime.gcd_eq_one hmk, one_mul]
  · rw [Nat.mul_div_cancel _ hk]

/-- **Lemma `lemma:gammagreaterpiover2`.** Suppose `3α + 2β = π`. Then `γ > π/2`. -/
theorem gammagreaterpiover2 {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (hrel : 3 * ∠ B A C + 2 * ∠ A B C = π) : π / 2 < ∠ A C B := by
  obtain ⟨-, -, -, hα, -, -, hsum, -⟩ := tri_facts hABC
  linarith

/-- **Lemma `lemma:primeimpliesjone`.** Suppose `j(m, k) = (M, K)`, with `M > 0` and
`N = 2K² - M² > 0`. Assume `N` is prime. Then `j = 1`.

The numbers are natural numbers: in the paper `j = gcd (M, K)`, so `j > 0`. Over `ℤ`,
`j = -1` would satisfy the hypotheses. -/
theorem primeimpliesjone (j m k M K N : ℕ) (hM : M = j * m) (hK : K = j * k) (hMpos : 0 < M)
    (heq : N + M ^ 2 = 2 * K ^ 2) (hN : N.Prime) : j = 1 := by
  subst hM hK
  have hj0 : j ≠ 0 := by rintro rfl; simp at hMpos
  -- `N = j²(2k² - m²)`, so `j² ∣ N`.
  have hdvd : j ^ 2 ∣ N := by
    have h : j ^ 2 ∣ N + (j * m) ^ 2 := by rw [heq]; exact ⟨2 * k ^ 2, by ring⟩
    exact (Nat.dvd_add_left ⟨m ^ 2, by ring⟩).mp h
  rcases hN.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact (Nat.pow_eq_one.mp h).resolve_right (by norm_num)
  · -- `j² = N` is impossible: a prime is not a square.
    exfalso
    have hj : j ∣ N := ⟨j, by rw [← h]; ring⟩
    rcases hN.eq_one_or_self_of_dvd _ hj with h1 | h1
    · subst h1; simp at h; exact hN.one_lt.ne h
    · rw [h1] at h
      have : N * (N - 1) = 0 := by
        rw [Nat.mul_sub, mul_one, ← sq, h, Nat.sub_self]
      rcases mul_eq_zero.mp this with h2 | h2
      · exact hN.ne_zero h2
      · have := hN.two_le; omega

/-- **Lemma `lemma:deltacoords`.** With `δ = α + β`: `α = π - 2δ`, `β = 3δ - π`, `γ = π - δ`, and
`π/3 < δ < π/2`. Normalizing `c = 1` and putting `s = a/c`: `s = 2 cos δ`, `0 < s < 1`,
`b = 1 - s²`, and `cos α = 1 - s²/2`. -/
theorem deltacoords {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (hrel : 3 * ∠ B A C + 2 * ∠ A B C = π) :
    let δ := ∠ B A C + ∠ A B C
    let s := dist B C / dist A B
    ∠ B A C = π - 2 * δ ∧ ∠ A B C = 3 * δ - π ∧ ∠ A C B = π - δ ∧ π / 3 < δ ∧ δ < π / 2 ∧
      s = 2 * cos δ ∧ 0 < s ∧ s < 1 ∧ dist C A / dist A B = 1 - s ^ 2 ∧
      cos (∠ B A C) = 1 - s ^ 2 / 2 := by
  intro δ s
  obtain ⟨-, -, -, hα, hβ, -, hsum, -⟩ := tri_facts hABC
  obtain ⟨-, h1, h2⟩ := singamma hABC hrel
  set x := ∠ B A C / 2 with hx
  have hxpos : 0 < x := by linarith
  have hx6 : x < π / 6 := by linarith
  have hcosδ : cos δ = sin x := by
    rw [show δ = π / 2 - x by simp only [δ]; linarith, cos_pi_div_two_sub]
  have hsx : 0 < sin x := sin_pos_of_pos_of_lt_pi hxpos (by linarith)
  have hsx2 : sin x < 1 / 2 := by
    rw [← sin_pi_div_six]
    exact sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hx6
  have hs : s = 2 * sin x := h1
  refine ⟨by simp only [δ]; linarith, by simp only [δ]; linarith, by simp only [δ]; linarith,
    by simp only [δ]; linarith, by simp only [δ]; linarith, by rw [hs, hcosδ], by rw [hs]; linarith,
    by rw [hs]; linarith, by rw [hs]; exact h2, ?_⟩
  rw [hs, show ∠ B A C = 2 * x by linarith, cos_two_mul]
  have := sin_sq_add_cos_sq x
  nlinarith

/-- **Lemma `lemma:sines`.** With `δ = α + β` and `s = 2 cos δ` (`= a/c`, `lemma:deltacoords`):
`sin α / sin δ = s`, `sin β / sin δ = 1 - s²`, `sin γ / sin δ = sin (α + β) / sin δ = 1`,
`sin 2α / sin δ = sin (α + 2β) / sin δ = s (2 - s²)`, and
`sin 3α / sin δ = sin 2β / sin δ = s (1 - s²)(3 - s²)`. -/
theorem sines {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hrel : 3 * α + 2 * β = π) :
    let δ := α + β
    let s := 2 * cos δ
    sin α / sin δ = s ∧ sin β / sin δ = 1 - s ^ 2 ∧ sin (2 * α + β) / sin δ = 1 ∧
      sin (α + β) / sin δ = 1 ∧ sin (2 * α) / sin δ = s * (2 - s ^ 2) ∧
      sin (α + 2 * β) / sin δ = s * (2 - s ^ 2) ∧
      sin (3 * α) / sin δ = s * (1 - s ^ 2) * (3 - s ^ 2) ∧
      sin (2 * β) / sin δ = s * (1 - s ^ 2) * (3 - s ^ 2) := by
  intro δ s
  have hsc := sin_sq_add_cos_sq δ
  have hπ := pi_pos
  have hsδ : 0 < sin δ := sin_pos_of_pos_of_lt_pi (by simp only [δ]; linarith)
    (by simp only [δ]; linarith)
  have hne := hsδ.ne'
  have Sα : sin α = 2 * sin δ * cos δ := by
    rw [show α = π - 2 * δ by simp only [δ]; linarith, sin_pi_sub, sin_two_mul]
  have Cα : cos α = 1 - 2 * cos δ ^ 2 := by
    rw [show α = π - 2 * δ by simp only [δ]; linarith, cos_pi_sub, cos_two_mul]; ring
  have Sβ : sin β = -(3 * sin δ - 4 * sin δ ^ 3) := by
    rw [show β = 3 * δ - π by simp only [δ]; linarith, sin_sub_pi, sin_three_mul]
  have Sγ : sin (2 * α + β) = sin δ := by
    rw [show 2 * α + β = π - δ by simp only [δ]; linarith, sin_pi_sub]
  have S2α : sin (2 * α) = 2 * sin α * cos α := sin_two_mul α
  have Sα2β : sin (α + 2 * β) = sin (2 * α) := by
    rw [show α + 2 * β = π - 2 * α by linarith, sin_pi_sub]
  have S3α : sin (3 * α) = 3 * sin α - 4 * sin α ^ 3 := sin_three_mul α
  have S2β : sin (2 * β) = sin (3 * α) := by
    rw [show 2 * β = π - 3 * α by linarith, sin_pi_sub]
  simp only [s]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [div_eq_iff hne]
  · rw [Sα]; ring
  · rw [Sβ]; linear_combination 4 * sin δ * hsc
  · rw [Sγ]; ring
  · ring
  · rw [S2α, Sα, Cα]; ring
  · rw [Sα2β, S2α, Sα, Cα]; ring
  · rw [S3α, Sα]; linear_combination (-32 * sin δ * cos δ ^ 3) * hsc
  · rw [S2β, S3α, Sα]; linear_combination (-32 * sin δ * cos δ ^ 3) * hsc


-- `a` and `b` are part of the printed hypotheses; the identities need only `c`.
set_option linter.unusedVariables false in
/-- **Lemma `lemma:singamma2`.** Suppose `3α + 2β = π` and let `s = 2 sin (α/2)`. Suppose the
triangle with sides `(a, b, c)` and angles `(α, β, γ)` is scaled by `κ`, so that
`(a, b, c) = κ (sin α, sin β, sin γ)`. Then `κ sin 2α / c = s (2 - s²)`, `sin 2α = (2 - s²) sin α`,
and `κ sin 2β / c = κ sin 3α / c = s (1 + s)(1 - s)(3 - s²)`. -/
theorem singamma2 {α β γ a b c κ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : α + β + γ = π)
    (hrel : 3 * α + 2 * β = π) (hκ : 0 < κ)
    (hsides : a = κ * sin α ∧ b = κ * sin β ∧ c = κ * sin γ) :
    let s := 2 * sin (α / 2)
    κ * sin (2 * α) / c = s * (2 - s ^ 2) ∧ sin (2 * α) = (2 - s ^ 2) * sin α ∧
      κ * sin (2 * β) / c = κ * sin (3 * α) / c ∧
      κ * sin (3 * α) / c = s * (1 + s) * (1 - s) * (3 - s ^ 2) := by
  intro s
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨r1, -, -, -, r5, -, r7, r8⟩ := r
  have hsδ : 0 < sin (α + β) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcs : 2 * cos (α + β) = s := by
    simp only [s]
    rw [show α + β = π / 2 - α / 2 by linarith, cos_pi_div_two_sub]
  have hc : c = κ * sin (α + β) := by
    rw [hsides.2.2, show γ = π - (α + β) by linarith, sin_pi_sub]
  rw [hcs] at r1 r5 r7 r8
  rw [div_eq_iff hsδ.ne'] at r1 r5 r7 r8
  have hκδ : κ * sin (α + β) ≠ 0 := by positivity
  rw [hc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_eq_iff hκδ, r5]; ring
  · rw [r5, r1]; ring
  · rw [r8, r7]
  · rw [div_eq_iff hκδ, r7]; ring

/-- The arithmetic of `lemma:gsquare`: integer sides with no common factor and `a² + bc = c²`. -/
theorem gsquare_arith (a b c m k : ℕ) (hb0 : 0 < b) (hc0 : 0 < c)
    (hgcd : Nat.gcd (Nat.gcd a b) c = 1) (hrel' : a ^ 2 + b * c = c ^ 2)
    (hmk : Nat.Coprime m k) (hk : 0 < k) (hratio : a * k = m * c) :
    a = m * k ∧ b = k ^ 2 - m ^ 2 ∧ c = k ^ 2 ∧ k = Nat.gcd a c ∧ m = a / k ∧ m < k := by
  -- `c = kt` and `a = mt`.
  obtain ⟨t, rfl⟩ : k ∣ c :=
    (Nat.Coprime.symm hmk).dvd_of_dvd_mul_left ⟨a, by rw [← hratio, mul_comm]⟩
  have hat : a = m * t := by
    apply Nat.eq_of_mul_eq_mul_left hk
    rw [mul_comm k a, hratio]
    ring
  subst hat
  have ht : 0 < t := Nat.pos_of_mul_pos_left hc0
  -- Cancelling `t`: `m²t + bk = k²t`.
  have h1 : m ^ 2 * t + b * k = k ^ 2 * t := by
    apply Nat.eq_of_mul_eq_mul_left ht
    linear_combination hrel'
  -- So `k ∣ m²t`, hence `k ∣ t`: `t = ku`.
  have hkt : k ∣ t := by
    have : k ∣ m ^ 2 * t := by
      have h2 : k ∣ m ^ 2 * t + b * k := by rw [h1]; exact ⟨k * t, by ring⟩
      exact (Nat.dvd_add_left (Dvd.intro_left b rfl)).mp h2
    exact (Nat.Coprime.pow_right 2 hmk.symm).dvd_of_dvd_mul_left this
  obtain ⟨u, rfl⟩ := hkt
  have h2 : m ^ 2 * u + b = k ^ 2 * u := by
    apply Nat.eq_of_mul_eq_mul_left hk
    linear_combination h1
  -- `u` divides `a`, `b` and `c`, so `u = 1`.
  have hu : u = 1 := by
    have hub : u ∣ b := by
      have : u ∣ m ^ 2 * u + b := by rw [h2]; exact Dvd.intro_left _ rfl
      exact (Nat.dvd_add_right (Dvd.intro_left _ rfl)).mp this
    have : u ∣ Nat.gcd (Nat.gcd (m * (k * u)) b) (k * (k * u)) :=
      Nat.dvd_gcd (Nat.dvd_gcd ⟨m * k, by ring⟩ hub) ⟨k * k, by ring⟩
    rw [hgcd] at this
    exact Nat.dvd_one.mp this
  subst hu
  simp only [mul_one] at h2 ⊢
  have hmk' : m < k := by
    have : m ^ 2 < k ^ 2 := by linarith
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp this
  refine ⟨trivial, by rw [← h2, Nat.add_sub_cancel_left], by ring, ?_, ?_, hmk'⟩
  · rw [Nat.gcd_mul_right, Nat.Coprime.gcd_eq_one hmk, one_mul]
  · rw [Nat.mul_div_cancel _ hk]

end TriangleTiling.ThreeAlpha
