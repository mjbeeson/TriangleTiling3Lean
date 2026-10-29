/-
Tilings of the isosceles triangle with base angles `α + β` (M. Beeson, *Triangle tiling: the
case 3α + 2β = π*, arXiv 1206.2229v4): `theorem:isoscelesconstruction`,
`corollary:isoscelesall`.

Statements not yet checked by Beeson. The tilings are Bonfioli's (`Erdos634.BeesonCor5`,
UNAUDITED); this file relabels the target so that the apex (angle `α`) is `B` and derives the
angles from the side lengths.
-/
import TriangleTiling.Laczkovich.ThreeAlphaConstrBase
import TriangleTiling.RightTile.Helper2
import Erdos634.Draft.BeesonCor5
import Erdos634.Draft.BeesonCor6
import TriangleTiling.ThreeAlpha.Complementary

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry EuclideanGeometry

variable {N : ℕ}

theorem oppLen_realScale (T : Tri) {s : ℝ} (hs : 0 < s) (k : Fin 3) :
    (Erdos634.Realizable.scaleTri s hs.ne' T).oppLen k = s * T.oppLen k := by
  unfold Tri.oppLen
  simp only [Erdos634.Realizable.scaleTri_pts]
  rw [Erdos634.Realizable.dist_homothety, abs_of_pos hs]

/-- Congruent triangles: sides opposite corresponding vertices are equal. -/
theorem oppLen_of_congruent {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ k, T.oppLen k = U.oppLen (σ k) := by
  obtain ⟨σ, -, hd⟩ := corner_perm_dist h
  refine ⟨σ, fun k => ?_⟩
  unfold Tri.oppLen
  rw [hd]
  have : ∀ ρ : Equiv.Perm (Fin 3), ∀ k, (ρ (k + 1) = ρ k + 1 ∧ ρ (k + 2) = ρ k + 2) ∨
      (ρ (k + 1) = ρ k + 2 ∧ ρ (k + 2) = ρ k + 1) := by decide
  rcases this σ k with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
  exact dist_comm _ _

/-- Bonfioli's isosceles tilings (`cor5`, `cor5_thm24`), in our vocabulary. -/
theorem iso_package (E : CongruentDissection N) (R : Erdos634.LaczL22.RTri) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (h : a * a + c * b = c * c)
    (hRa : R.a = (a : ℚ)) (hRb : R.b = (b : ℚ)) (hRc : R.c = (c : ℚ)) {s : ℝ} (hs : 0 < s)
    (hiso : dist (E.target.pts 2) (E.target.pts 0) = dist (E.target.pts 2) (E.target.pts 1))
    (hap : cornerAngle (E.target.pts 0) (E.target.pts 2) (E.target.pts 1)
      = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2))
    (hcong : E.model.Congruent (Erdos634.Realizable.scaleTri s hs.ne' R.Δ)) :
    ∃ D : CongruentDissection N, ∃ α β : ℝ,
      TileSides D α β (2 * α + β) (s * a) (s * b) (s * c) ∧ 3 * α + 2 * β = Real.pi ∧
      D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β := by
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at h; omega
    · exact h0
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hh : (a : ℝ) * a + c * b = c * c := by exact_mod_cast h
  have R0 : R.Δ.oppLen 0 = a := by
    show dist (R.Δ.pts 1) (R.Δ.pts 2) = _; rw [R.ha, hRa]; push_cast; rfl
  have R1 : R.Δ.oppLen 1 = b := by
    show dist (R.Δ.pts 2) (R.Δ.pts 0) = _; rw [R.hb, hRb]; push_cast; rfl
  have R2 : R.Δ.oppLen 2 = c := by
    show dist (R.Δ.pts 0) (R.Δ.pts 1) = _; rw [R.hc, hRc]; push_cast; rfl
  obtain ⟨σ, hσ⟩ := oppLen_of_congruent hcong
  have l : ∀ j, E.model.oppLen (σ.symm j) = s * R.Δ.oppLen j := by
    intro j; rw [hσ, Equiv.apply_symm_apply, oppLen_realScale _ hs]
  have hrelb : s * (b : ℝ) = s * c - (s * a) ^ 2 / (s * c) := by
    field_simp; linarith
  obtain ⟨hTS, h32, cα, -⟩ := tile_of_sides E σ.symm (by rw [l, R0]) (by rw [l, R1]) (by rw [l, R2])
    hrelb
  set α := E.model.angleAt (σ.symm 0)
  set β := E.model.angleAt (σ.symm 1)
  obtain ⟨hα, hβ, hγ, -⟩ := model_facts E h32 hTS
  rw [hγ] at hTS
  have hπ := Real.pi_pos
  -- the apex angle is `α`
  have hapex : E.target.angleAt 2 = α := by
    show cornerAngle (E.target.pts 0) (E.target.pts 2) (E.target.pts 1) = α
    rw [hap]
    show R.Δ.angleAt 0 = α
    refine angleAt_eq_of_cos R.Δ 0 hα.le (by linarith) ?_
    rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, R0, R1, R2]
    have : s ^ 2 * ((a : ℝ) ^ 2 - (b ^ 2 + c ^ 2 - 2 * b * c * Real.cos α)) = 0 := by
      linear_combination cα
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (by positivity)
    · linarith
  -- base angles are equal
  have hbase : E.target.angleAt 0 = E.target.angleAt 1 := by
    show ∠ (E.target.pts 1) (E.target.pts 0) (E.target.pts 2) =
      ∠ (E.target.pts 2) (E.target.pts 1) (E.target.pts 0)
    rw [EuclideanGeometry.angle_comm]
    exact EuclideanGeometry.angle_eq_angle_of_dist_eq hiso
  have hsum := E.target.angleAt_sum
  refine ⟨relabelTarget E (Equiv.swap 1 2), α, β, hTS, h32, ?_, ?_, ?_⟩
  · rw [relabelTarget_target, angleAt_relabel, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    linarith
  · rw [relabelTarget_target, angleAt_relabel, Equiv.swap_apply_left]; exact hapex
  · rw [relabelTarget_target, angleAt_relabel, Equiv.swap_apply_right]; linarith

/-- Rescaling a tiling so that the tile has the given sides. -/
theorem unscale {D : CongruentDissection N} {α β γ a b c s : ℝ} (hs : 0 < s)
    (hT : TileSides D α β γ (s * a) (s * b) (s * c)) :
    ∃ D' : CongruentDissection N, TileSides D' α β γ a b c ∧
      ∀ k, D'.target.angleAt k = D.target.angleAt k := by
  have hr : 0 < 1 / s := by positivity
  refine ⟨scaleDissection D hr, ?_, fun k => scale_angleAt _ hr.ne' _⟩
  have := tileSides_scale hT hr (D' := scaleDissection D hr) rfl
  have e : ∀ x : ℝ, 1 / s * (s * x) = x := fun x => by field_simp
  rwa [e, e, e] at this

/-- **Theorem `theorem:isoscelesconstruction`.** Let the tile `(a, b, c)` have angles
`(α, β, γ)` with `3α + 2β = π`, let `a, b, c` be integers with no common factor (so `c ∣ a²`), and
suppose `a²c < b(a² + b²)`. Then for some `N`, some isosceles triangle with base angles `α + β` can
be `N`-tiled by the tile.

`3α + 2β = π` is given in the form `a² + cb = c²` (`lemma:anglesOK`); the conclusion gives the
angles. The isosceles triangle is `ABC` with apex `B`. -/
theorem isoscelesconstruction (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a * a + c * b = c * c)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) (hlt : a * a * c < b * (a * a + b * b)) :
    ∃ (N : ℕ) (D : CongruentDissection N) (α β : ℝ),
      TileSides D α β (2 * α + β) a b c ∧ 3 * α + 2 * β = Real.pi ∧
      D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β := by
  obtain ⟨R, hRa, hRb, hRc⟩ := Erdos634.BeesonCor6.exists_RTri_of_nat a b c ha hb h
  obtain ⟨s, hs, N, E, hiso, hap, hcong⟩ :=
    Erdos634.BeesonCor5.cor5_thm24 a b c ha hb h hg hlt R hRa hRb hRc
  obtain ⟨D, α, β, hT, h32, A0, A1, A2⟩ := iso_package E R a b c ha hb h hRa hRb hRc hs hiso hap hcong
  obtain ⟨D', hT', hA⟩ := unscale hs hT
  exact ⟨N, D', α, β, hT', h32, by rw [hA, A0], by rw [hA, A1], by rw [hA, A2]⟩

/-- `2 sin(α/2)` rational in `(0, 1)`: `p/r` in lowest terms. -/
theorem rat_pr {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hα : 0 < α) (hβ : 0 < β)
    (hrat : ∃ q : ℚ, 2 * Real.sin (α / 2) = q) :
    ∃ p r : ℕ, 0 < p ∧ p < r ∧ Nat.Coprime p r ∧ 2 * Real.sin (α / 2) = (p : ℝ) / r := by
  obtain ⟨q, hq⟩ := hrat
  have hπ := Real.pi_pos
  have hs0 : 0 < Real.sin (α / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs1 : Real.sin (α / 2) < 1 / 2 := by
    rw [← Real.sin_pi_div_six]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hq0 : (0 : ℝ) < q := by rw [← hq]; linarith
  have hq1 : (q : ℝ) < 1 := by rw [← hq]; linarith
  have h0 : 0 ≤ q.num := Rat.num_nonneg.mpr (by exact_mod_cast hq0.le)
  have hnum : (q.num : ℝ) = (q.num.toNat : ℕ) := by
    rw [show ((q.num.toNat : ℕ) : ℝ) = ((q.num.toNat : ℤ) : ℝ) by norm_cast, Int.toNat_of_nonneg h0]
  have hqpr : (q : ℝ) = (q.num.toNat : ℕ) / q.den := by
    rw [← hnum]; exact_mod_cast (Rat.num_div_den q).symm
  have hr : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  refine ⟨q.num.toNat, q.den, ?_, ?_, ?_, by rw [hq, hqpr]⟩
  · have : (0 : ℝ) < (q.num.toNat : ℕ) := by rw [hqpr] at hq0; exact (div_pos_iff_of_pos_right hr).mp hq0
    exact_mod_cast this
  · have : ((q.num.toNat : ℕ) : ℝ) < q.den := by rw [hqpr, div_lt_one hr] at hq1; exact hq1
    exact_mod_cast this
  · have e : q.num.toNat = q.num.natAbs := by omega
    rw [e]; exact q.reduced

/-- From one of Bonfioli's isosceles tilings by the integer tile `(pr, r² - p², r²)` with
`p/r = 2 sin(α/2)`: a tiling with base angles `α + β` by the tile with angles `(α, β, γ)`. -/
theorem iso_finish {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hα : 0 < α) (hα3 : α < Real.pi / 3) {p r : ℕ} (hpr : p < r)
    (hpq : 2 * Real.sin (α / 2) = (p : ℝ) / r) (E : CongruentDissection N) (R : Erdos634.LaczL22.RTri)
    (ha0 : 0 < p * r) (hb0 : 0 < r * r - p * p) (h0 : p * r * (p * r) + r * r * (r * r - p * p) = r * r * (r * r))
    (hRa : R.a = ((p * r : ℕ) : ℚ)) (hRb : R.b = ((r * r - p * p : ℕ) : ℚ)) (hRc : R.c = ((r * r : ℕ) : ℚ))
    {s : ℝ} (hs : 0 < s)
    (hiso : dist (E.target.pts 2) (E.target.pts 0) = dist (E.target.pts 2) (E.target.pts 1))
    (hap : cornerAngle (E.target.pts 0) (E.target.pts 2) (E.target.pts 1)
      = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2))
    (hcong : E.model.Congruent (Erdos634.Realizable.scaleTri s hs.ne' R.Δ)) :
    ∃ (D : CongruentDissection N) (a b c : ℝ), TileSides D α β (2 * α + β) a b c ∧
      D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β := by
  obtain ⟨D, α', β', hT, h32, A0, A1, A2⟩ := iso_package E R _ _ _ ha0 hb0 h0 hRa hRb hRc hs hiso hap hcong
  obtain ⟨hα', hβ', -, -⟩ := model_facts D h32 hT
  have hr : (0 : ℝ) < r := by have : 0 < r := by omega
                              exact_mod_cast this
  have heq : α' = α := by
    have := s_eq h32 hT
    rw [show s * ((p * r : ℕ) : ℝ) / (s * ((r * r : ℕ) : ℝ)) = p / r by push_cast; field_simp, ← hpq] at this
    exact alpha_eq_of_sin hα' (by linarith) hα hα3 this.symm
  subst heq
  have hβeq : β' = β := by linarith
  subst hβeq
  exact ⟨D, _, _, _, hT, A0, A1, A2⟩

/-- The real root `x₀ ≈ 0.5698` of `x³ = (1 - x)²` exists. -/
theorem x0_exists : ∃ x₀ : ℝ, x₀ ^ 3 = (1 - x₀) ^ 2 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 - x ^ 2 + 2 * x - 1) (Set.Icc 0 1) := by fun_prop
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc (zero_le_one) hc (show (0 : ℝ) ∈ Set.Icc _ _ by norm_num)
  exact ⟨x, by simp only at hx; linarith⟩

/-- **Theorem `theorem:Lconstruction`** (Laczkovich's construction). Suppose `3α + 2β = π`, and
let `ABC` be an isosceles triangle with base angles `α + β`. Suppose the tile is rational and
`b/c < x₀`, where `x₀ ≈ 0.5698` is the real root of `x³ = (1 - x)²`. Then for some `N`, there is an
`N`-tiling of a triangle similar to `ABC` by the tile `(α, β, γ)`, where `γ = 2α + β`.

"Rational" is `s = 2 sin(α/2)` rational; `b/c = 1 - s²`. The tiling is Bonfioli's `cor5_fourth`
(Laczkovich 1995, Theorem 2.4). -/
theorem Lconstruction {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hα : 0 < α) (hβ : 0 < β)
    (hrat : ∃ q : ℚ, 2 * Real.sin (α / 2) = q)
    (hx : ∃ x₀ : ℝ, x₀ ^ 3 = (1 - x₀) ^ 2 ∧ 1 - (2 * Real.sin (α / 2)) ^ 2 < x₀) :
    ∃ (N : ℕ) (D : CongruentDissection N) (a b c : ℝ), TileSides D α β (2 * α + β) a b c ∧
      D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β := by
  have hπ := Real.pi_pos
  obtain ⟨p, r, hp, hpr, hcop, hpq⟩ := rat_pr hrel hα hβ hrat
  obtain ⟨ha0, hb0, h0, -⟩ := Erdos634.BeesonCor6.coprime_tile p r hp hpr hcop
  obtain ⟨R, hRa, hRb, hRc⟩ := Erdos634.BeesonCor6.exists_RTri_of_nat _ _ _ ha0 hb0 h0
  obtain ⟨x₀, hx₀, hlt⟩ := hx
  have hle : p * p ≤ r * r := Nat.mul_le_mul hpr.le hpr.le
  have hr : (0 : ℝ) < r := by have : 0 < r := by omega
                              exact_mod_cast this
  -- `b³ < c (c - b)²`, from `b/c < x₀`
  have hcube : (((r * r - p * p : ℕ) : ℝ)) ^ 3 < ((r * r : ℕ) : ℝ) * (((r * r : ℕ) : ℝ) - ((r * r - p * p : ℕ) : ℝ)) ^ 2 := by
    set x := 1 - ((p : ℝ) / r) ^ 2
    have hf : x ^ 3 - x ^ 2 + 2 * x - 1 < 0 := by
      have := f_strictMono (show x < x₀ by rw [hpq] at hlt; exact hlt)
      simp only at this; nlinarith [this, hx₀]
    have hb : ((r * r - p * p : ℕ) : ℝ) = (r : ℝ) ^ 2 * x := by
      push_cast [hle]; simp only [x]; field_simp
    have hc : ((r * r : ℕ) : ℝ) = (r : ℝ) ^ 2 := by push_cast; ring
    rw [hb, hc]
    have hr2 : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
    have : (r : ℝ) ^ 2 * (r ^ 2 - r ^ 2 * x) ^ 2 - ((r : ℝ) ^ 2 * x) ^ 3 =
        -((r : ℝ) ^ 2) ^ 3 * (x ^ 3 - x ^ 2 + 2 * x - 1) := by ring
    nlinarith [mul_pos (pow_pos hr2 3) (neg_pos.mpr hf)]
  have hbc : r * r - p * p < r * r := Nat.sub_lt (Nat.mul_pos (by omega) (by omega)) (Nat.mul_pos hp hp)
  obtain ⟨s, hs, N, E, hiso, hap, hcong⟩ :=
    Erdos634.BeesonCor5.cor5_fourth _ _ _ ha0 hb0 hbc h0 hcube R hRa hRb hRc
  obtain ⟨D, a, b, c, hT, A0, A1, A2⟩ :=
    iso_finish hrel hα (by linarith) hpr hpq E R ha0 hb0 h0 hRa hRb hRc hs hiso hap hcong
  exact ⟨N, D, a, b, c, hT, A0, A1, A2⟩

/-- **Corollary `corollary:isoscelesall`.** Let `3α + 2β = π` and suppose the tile `(α, β, γ)` is
rational. Then for some `N`, some isosceles triangle with base angles `α + β` can be `N`-tiled by
the tile.

As printed: by `lemma:complementary` either Laczkovich's construction (`theorem:Lconstruction`) or
`theorem:isoscelesconstruction` applies. "Rational" is read as `s = 2 sin(α/2)` rational; "by the
tile" as by a tile with angles `(α, β, γ)`. The isosceles triangle is `ABC` with apex `B`. -/
theorem isoscelesall {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hα : 0 < α) (hβ : 0 < β)
    (hrat : ∃ q : ℚ, 2 * Real.sin (α / 2) = q) :
    ∃ (N : ℕ) (D : CongruentDissection N) (a b c : ℝ), TileSides D α β (2 * α + β) a b c ∧
      D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β := by
  have hπ := Real.pi_pos
  obtain ⟨p, r, hp, hpr, hcop, hpq⟩ := rat_pr hrel hα hβ hrat
  obtain ⟨ha0, hb0, h0, hgcd⟩ := Erdos634.BeesonCor6.coprime_tile p r hp hpr hcop
  set a := p * r
  set b := r * r - p * p
  set c := r * r
  have hle : p * p ≤ r * r := Nat.mul_le_mul hpr.le hpr.le
  have hr : (0 : ℝ) < r := by have : 0 < r := by omega
                              exact_mod_cast this
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb0
  have hcR : (0 : ℝ) < c := by simp only [c]; push_cast; positivity
  have hrelR : (b : ℝ) = c - (a : ℝ) ^ 2 / c := by
    simp only [a, b, c]; push_cast [hle]; field_simp
  have hbcq : ∃ q : ℚ, (b : ℝ) / c = q := ⟨(b : ℚ) / c, by push_cast; rfl⟩
  obtain ⟨-, -, hxor, hx0⟩ := complementary hbR hcR hrelR
  rcases hxor hbcq with ⟨h1, -⟩ | ⟨h2, -⟩
  · -- (i): Laczkovich's construction
    obtain ⟨x₀, hx₀⟩ := x0_exists
    refine Lconstruction hrel hα hβ hrat ⟨x₀, hx₀, ?_⟩
    have := ((hx0 x₀ hx₀).1).mp h1
    rw [hpq]
    have e : (b : ℝ) / c = 1 - ((p : ℝ) / r) ^ 2 := by
      simp only [b, c]; push_cast [hle]; field_simp
    rwa [e] at this
  · -- (ii): `theorem:isoscelesconstruction`
    have hlt : a * a * c < b * (a * a + b * b) := by
      have : ((a * a * c : ℕ) : ℝ) < ((b * (a * a + b * b) : ℕ) : ℝ) := by push_cast; nlinarith [h2]
      exact_mod_cast this
    obtain ⟨N, D, α', β', hT, h32, A0, A1, A2⟩ := isoscelesconstruction a b c ha0 hb0 h0 hgcd hlt
    obtain ⟨hα', hβ', -, -⟩ := model_facts D h32 hT
    have heq : α' = α := by
      have := s_eq h32 hT
      rw [show ((a : ℕ) : ℝ) / ((c : ℕ) : ℝ) = p / r by simp only [a, c]; push_cast; field_simp,
        ← hpq] at this
      exact alpha_eq_of_sin hα' (by linarith) hα (by linarith) this.symm
    subst heq
    have hβeq : β' = β := by linarith
    subst hβeq
    exact ⟨N, D, _, _, _, hT, A0, A1, A2⟩

end TriangleTiling.ThreeAlpha
