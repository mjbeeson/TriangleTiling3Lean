/-
`theorem:M1M2` (Section 5) and Section 6 ("Rationality of the tile") of M. Beeson, *Triangle tiling:
the case 3α + 2β = π* (arXiv 1206.2229v4), for the shapes other than the triquadratic one.

Hypotheses throughout, as in the paper: `3α + 2β = π`; `ABC` is `N`-tiled by copies of the tile
`T` with angles `(α, β, γ)` and sides `(a, b, c)`; `ABC` is not similar to `T`; `A`, `B`, `C` are in
counterclockwise order with the angles listed at `A`, `B`, `C`; `M₁`, `M₂` are the integers of
`theorem:Mdef` for `Φ₁`, `Φ₂` normalized as in `lemma:Phisigns`. We write `s = a/c` and
`Λ` for the ratio of circumdiameters (`Lam`); the paper normalizes `c = 1`.
-/
import TriangleTiling.Laczkovich.ThreeAlphaPhi
import TriangleTiling.ThreeAlpha.Areas

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)

variable {N : ℕ} (D : CongruentDissection N)


/-- `Φ(∂ABC) = |AB| Φ(AB) + |BC| Φ(BC) + |CA| Φ(CA)`. -/
theorem PhiR_target (Φ : Real.Angle → ℝ) (T : Tri) :
    PhiR Φ T = T.oppLen 2 * Φ (T.leftUnit 0).angle + T.oppLen 0 * Φ (T.leftUnit 1).angle
      + T.oppLen 1 * Φ (T.leftUnit 2).angle := by
  unfold PhiR Tri.flux Tri.oppLen
  simp only [Fin.sum_univ_three, smul_eq_mul]
  rfl

/-- The sides of `ABC`: `|side k| = Λ c sin(angle k) / sin δ`. -/
theorem target_side {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (k : Fin 3) :
    D.target.oppLen k = Lam D * c * (Real.sin (D.target.angleAt k) / Real.sin (α + β)) := by
  obtain ⟨-, -, -, hS, hc, -, -, -, -, hdm, -⟩ := model_facts D hrel hT
  have hd := circumdiam_pos D.model
  rw [lawsin D.target k, Lam, hdm]
  field_simp

/-- **Theorem `theorem:M1M2`.** Let `ABC` be one of the five shapes of `lemma:shapes`, tiled by
copies of `T`. Then

| angles of `ABC` | `M₁` | `M₂` |
|---|---|---|
| `(2α, β, α + β)` | `Λ s` | `Λ s` |
| `(β, 3α, β)` | `Λ(1 - s)(1 + s)²` | `-Λ(1 - s)²(1 + s)` |
| `(α + β, α, α + β)` | `Λ/(1 + s)` | `-Λ/(1 - s)` |
| `(α, α + 2β, α)` | `Λ s(2 + s)/(1 + s)` | `-Λ s(2 - s)/(1 - s)` |
| `(2α, α, 2β)` | `Λ s(1 - s)(2 + s)` | `-Λ s(2 - s)(1 + s)` |

In particular `M₁ ≠ 0` and `M₂ ≠ 0`, and `Λ = M₁/s` in the first row. -/
theorem M1M2 {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) (hccw : 0 < D.target.det)
    {M₁ M₂ : ℤ} (h₁ : PhiR (Phi1 (α + β) (baseDir D)) D.target = M₁ * (a + b + c))
    (h₂ : PhiR (Phi2 (α + β) (baseDir D)) D.target = M₂ * (a - b - c)) :
    let s := a / c
    let Λ := Lam D
    let shape := fun x y z : ℝ =>
      D.target.angleAt 0 = x ∧ D.target.angleAt 1 = y ∧ D.target.angleAt 2 = z
    (shape (2 * α) β (α + β) → (M₁ : ℝ) = Λ * s ∧ (M₂ : ℝ) = Λ * s) ∧
    (shape β (3 * α) β →
      (M₁ : ℝ) = Λ * (1 - s) * (1 + s) ^ 2 ∧ (M₂ : ℝ) = -Λ * (1 - s) ^ 2 * (1 + s)) ∧
    (shape (α + β) α (α + β) → (M₁ : ℝ) = Λ / (1 + s) ∧ (M₂ : ℝ) = -Λ / (1 - s)) ∧
    (shape α (α + 2 * β) α →
      (M₁ : ℝ) = Λ * s * (2 + s) / (1 + s) ∧ (M₂ : ℝ) = -Λ * s * (2 - s) / (1 - s)) ∧
    (shape (2 * α) α (2 * β) →
      (M₁ : ℝ) = Λ * s * (1 - s) * (2 + s) ∧ (M₂ : ℝ) = -Λ * s * (2 - s) * (1 + s)) ∧
    ((shape (2 * α) β (α + β) ∨ shape β (3 * α) β ∨ shape (α + β) α (α + β) ∨
        shape α (α + 2 * β) α ∨ shape (2 * α) α (2 * β)) → M₁ ≠ 0 ∧ M₂ ≠ 0) ∧
    (shape (2 * α) β (α + β) → Λ = M₁ / s) := by
  intro s Λ shape
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  obtain ⟨hα, hβ, hγ, hS, hc, ha, hb, ht0, ht1, -, -⟩ := model_facts D hrel hT
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨r1, r2, -, -, r5, r6, r7, r8⟩ := r
  rw [div_eq_iff hS.ne'] at r1 r2 r5 r6 r7 r8
  have sg := Phisigns D hrel hT' hns hccw
  dsimp only at sg
  obtain ⟨⟨p1, p2⟩, g1, g2, g3, g4, g5⟩ := sg
  set t := 2 * Real.cos (α + β)
  have hst : s = t := by simp only [s]; rw [ha]; field_simp
  have habc : a + b + c ≠ 0 := ne_of_gt (by
    rw [ha, hb]
    have : 0 < 2 + t - t ^ 2 := by nlinarith
    nlinarith [mul_pos hc this])
  have habc' : a - b - c ≠ 0 := ne_of_lt (by
    rw [ha, hb]
    have : 0 < 2 - t - t ^ 2 := by nlinarith
    nlinarith [mul_pos hc this])
  have hΛ : 0 < Λ := div_pos (circumdiam_pos _) (circumdiam_pos _)
  have eM1 : (M₁ : ℝ) = PhiR (Phi1 (α + β) (baseDir D)) D.target / (a + b + c) := by
    rw [h₁]; field_simp
  have eM2 : (M₂ : ℝ) = PhiR (Phi2 (α + β) (baseDir D)) D.target / (a - b - c) := by
    rw [h₂]; field_simp
  rw [PhiR_target] at eM1 eM2
  simp only [target_side D hrel hT] at eM1 eM2
  rw [p1] at eM1
  rw [p2] at eM2
  have h1t : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have h1t' : 1 - t ≠ 0 := ne_of_gt (by linarith)
  have row1 : shape (2 * α) β (α + β) → (M₁ : ℝ) = Λ * s ∧ (M₂ : ℝ) = Λ * s := by
    rintro ⟨e0, e1, e2⟩
    obtain ⟨b1, c1, b2, c2⟩ := g1 ⟨e0, e1, e2⟩
    rw [b1, c1, e0, e1, e2, r5, r2] at eM1
    rw [b2, c2, e0, e1, e2, r5, r2] at eM2
    rw [hst, eM1, eM2]
    have hS' := hS.ne'
    constructor <;> field_simp <;> rw [ha, hb] <;> ring
  have row2 : shape β (3 * α) β →
      (M₁ : ℝ) = Λ * (1 - s) * (1 + s) ^ 2 ∧ (M₂ : ℝ) = -Λ * (1 - s) ^ 2 * (1 + s) := by
    rintro ⟨e0, e1, e2⟩
    obtain ⟨b1, c1, b2, c2⟩ := g2 ⟨e0, e1, e2⟩
    rw [b1, c1, e0, e1, e2, r2, r7] at eM1
    rw [b2, c2, e0, e1, e2, r2, r7] at eM2
    rw [hst, eM1, eM2]
    have hS' := hS.ne'
    constructor <;> field_simp <;> rw [ha, hb] <;> ring
  have row3 : shape (α + β) α (α + β) → (M₁ : ℝ) = Λ / (1 + s) ∧ (M₂ : ℝ) = -Λ / (1 - s) := by
    rintro ⟨e0, e1, e2⟩
    obtain ⟨b1, c1, b2, c2⟩ := g3 ⟨e0, e1, e2⟩
    rw [b1, c1, e0, e1, e2, r1] at eM1
    rw [b2, c2, e0, e1, e2, r1] at eM2
    rw [hst, eM1, eM2]
    have hS' := hS.ne'
    constructor <;> field_simp <;> rw [ha, hb] <;> ring
  have row4 : shape α (α + 2 * β) α →
      (M₁ : ℝ) = Λ * s * (2 + s) / (1 + s) ∧ (M₂ : ℝ) = -Λ * s * (2 - s) / (1 - s) := by
    rintro ⟨e0, e1, e2⟩
    obtain ⟨b1, c1, b2, c2⟩ := g4 ⟨e0, e1, e2⟩
    rw [b1, c1, e0, e1, e2, r1, r6] at eM1
    rw [b2, c2, e0, e1, e2, r1, r6] at eM2
    rw [hst, eM1, eM2]
    have hS' := hS.ne'
    constructor <;> field_simp <;> rw [ha, hb] <;> ring
  have row5 : shape (2 * α) α (2 * β) →
      (M₁ : ℝ) = Λ * s * (1 - s) * (2 + s) ∧ (M₂ : ℝ) = -Λ * s * (2 - s) * (1 + s) := by
    rintro ⟨e0, e1, e2⟩
    obtain ⟨b1, c1, b2, c2⟩ := g5 ⟨e0, e1, e2⟩
    rw [b1, c1, e0, e1, e2, r5, r1, r8] at eM1
    rw [b2, c2, e0, e1, e2, r5, r1, r8] at eM2
    rw [hst, eM1, eM2]
    have hS' := hS.ne'
    constructor <;> field_simp <;> rw [ha, hb] <;> ring
  refine ⟨row1, row2, row3, row4, row5, ?_, fun h => ?_⟩
  · rw [hst] at row1 row2 row3 row4 row5
    have hp : 0 < Λ * t := mul_pos hΛ ht0
    have ne : ∀ (x : ℝ) (m : ℤ), (m : ℝ) = x → x ≠ 0 → m ≠ 0 := fun x m hm hx h0 =>
      hx (by rw [← hm, h0, Int.cast_zero])
    rintro (h | h | h | h | h)
    · obtain ⟨e1, e2⟩ := row1 h
      exact ⟨ne _ _ e1 hp.ne', ne _ _ e2 hp.ne'⟩
    · obtain ⟨e1, e2⟩ := row2 h
      exact ⟨ne _ _ e1 (by positivity), ne _ _ e2 (by
        have : 0 < Λ * (1 - t) ^ 2 * (1 + t) := by positivity
        linarith)⟩
    · obtain ⟨e1, e2⟩ := row3 h
      exact ⟨ne _ _ e1 (by positivity), ne _ _ e2 (by
        have : 0 < Λ / (1 - t) := div_pos hΛ (by linarith)
        rw [neg_div]; linarith)⟩
    · obtain ⟨e1, e2⟩ := row4 h
      exact ⟨ne _ _ e1 (by positivity), ne _ _ e2 (by
        have : 0 < Λ * t * (2 - t) / (1 - t) := div_pos (by
          have : 0 < 2 - t := by linarith
          positivity) (by linarith)
        rw [show -Λ * t * (2 - t) / (1 - t) = -(Λ * t * (2 - t) / (1 - t)) by ring]; linarith)⟩
    · obtain ⟨e1, e2⟩ := row5 h
      exact ⟨ne _ _ e1 (by
        have : 0 < 1 - t := by linarith
        positivity), ne _ _ e2 (by
        have : 0 < Λ * t * (2 - t) * (1 + t) := by
          have : 0 < 2 - t := by linarith
          positivity
        linarith)⟩
  · rw [(row1 h).1, hst]; field_simp


/-- A tile `(t c, (1 - t²) c, c)` with `t` rational is rational. -/
theorem rationalTile_of {a b c t : ℝ} (hc : 0 < c) (ha : a = t * c) (hb : b = (1 - t ^ 2) * c)
    (ht0 : 0 < t) (ht1 : t < 1) {q : ℚ} (hq : t = q) : RationalTile a b c := by
  have h1 : (1 : ℝ) - t ^ 2 ≠ 0 := by nlinarith
  subst ha hb hq
  refine ⟨⟨q, by field_simp⟩, ⟨1 - q ^ 2, by push_cast; field_simp⟩, ⟨q / (1 - q ^ 2), ?_⟩⟩
  push_cast; field_simp

/-- **Lemma `lemma:kappa`.** With `κ = (M₁ + M₂)/(M₂ - M₁)`: if `ABC` is triquadratic
(`(2α, β, α + β)`) then `M₁ = M₂` and `κ` is undefined. Otherwise `κ` is defined, and
`κ = -s`, `κ = s`, `κ = s/(2 - s²)`, `κ = s/(2 - s²)` for the shapes `(β, 3α, β)`,
`(α + β, α, α + β)`, `(α, α + 2β, α)`, `(2α, α, 2β)` respectively. In the last two cases
`0 < κ < 1` and `s = κ(2 - s²)`, equivalently `κ²s⁴ - (4κ² + 1)s² + 4κ² = 0`. -/
theorem kappa {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) (hccw : 0 < D.target.det)
    {M₁ M₂ : ℤ} (h₁ : PhiR (Phi1 (α + β) (baseDir D)) D.target = M₁ * (a + b + c))
    (h₂ : PhiR (Phi2 (α + β) (baseDir D)) D.target = M₂ * (a - b - c)) :
    let s := a / c
    let κ : ℝ := (M₁ + M₂) / (M₂ - M₁)
    let shape := fun x y z : ℝ =>
      D.target.angleAt 0 = x ∧ D.target.angleAt 1 = y ∧ D.target.angleAt 2 = z
    (shape (2 * α) β (α + β) → M₁ = M₂) ∧
    (shape β (3 * α) β → M₁ ≠ M₂ ∧ κ = -s) ∧
    (shape (α + β) α (α + β) → M₁ ≠ M₂ ∧ κ = s) ∧
    (shape α (α + 2 * β) α ∨ shape (2 * α) α (2 * β) →
      M₁ ≠ M₂ ∧ κ = s / (2 - s ^ 2) ∧ 0 < κ ∧ κ < 1 ∧ s = κ * (2 - s ^ 2) ∧
        κ ^ 2 * s ^ 4 - (4 * κ ^ 2 + 1) * s ^ 2 + 4 * κ ^ 2 = 0) := by
  intro s κ shape
  have m := M1M2 D hrel hT hns hccw h₁ h₂
  dsimp only at m
  obtain ⟨m1, m2, m3, m4, m5, -, -⟩ := m
  obtain ⟨-, -, -, -, hc, ha, -, ht0, ht1, -, -⟩ := model_facts D hrel hT
  have hst : a / c = 2 * Real.cos (α + β) := by rw [ha]; field_simp
  have hΛ : 0 < Lam D := div_pos (circumdiam_pos _) (circumdiam_pos _)
  rw [hst] at m1 m2 m3 m4 m5
  set t := 2 * Real.cos (α + β)
  have h1p : 0 < 1 + t := by linarith
  have h1m : 0 < 1 - t := by linarith
  have h2 : 0 < 2 - t ^ 2 := by nlinarith
  have hκ : κ = (M₁ + M₂) / (M₂ - M₁) := rfl
  simp only [s, hst]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨e1, e2⟩ := m1 h
    exact_mod_cast e1.trans e2.symm
  · obtain ⟨e1, e2⟩ := m2 h
    have hd : (M₂ : ℝ) - M₁ ≠ 0 := by
      rw [e1, e2]; apply ne_of_lt
      have : 0 < Lam D * (1 - t) * (1 + t) * 2 := by positivity
      nlinarith
    refine ⟨fun e => hd (by rw [e]; ring), ?_⟩
    rw [hκ, div_eq_iff hd, e1, e2]; ring
  · obtain ⟨e1, e2⟩ := m3 h
    have hd : (M₂ : ℝ) - M₁ ≠ 0 := by
      rw [e1, e2]; apply ne_of_lt
      have : 0 < Lam D / (1 + t) := by positivity
      have : 0 < Lam D / (1 - t) := by positivity
      rw [neg_div]; linarith
    refine ⟨fun e => hd (by rw [e]; ring), ?_⟩
    rw [hκ, div_eq_iff hd, e1, e2]; field_simp; ring
  · have hv : (M₂ : ℝ) - M₁ ≠ 0 ∧ ((M₁ : ℝ) + M₂) / (M₂ - M₁) = t / (2 - t ^ 2) := by
      rcases h with h | h
      · obtain ⟨e1, e2⟩ := m4 h
        have hd : (M₂ : ℝ) - M₁ ≠ 0 := by
          rw [e1, e2]; apply ne_of_lt
          have : 0 < Lam D * t * (2 + t) / (1 + t) := by positivity
          have : 0 < Lam D * t * (2 - t) / (1 - t) := by
            have : 0 < 2 - t := by linarith
            positivity
          rw [show -Lam D * t * (2 - t) / (1 - t) = -(Lam D * t * (2 - t) / (1 - t)) by ring]
          linarith
        refine ⟨hd, ?_⟩
        rw [div_eq_div_iff hd h2.ne', e1, e2]; field_simp; ring
      · obtain ⟨e1, e2⟩ := m5 h
        have hd : (M₂ : ℝ) - M₁ ≠ 0 := by
          rw [e1, e2]; apply ne_of_lt
          have : 0 < Lam D * t * (1 - t) * (2 + t) := by positivity
          have : 0 < Lam D * t * (2 - t) * (1 + t) := by
            have : 0 < 2 - t := by linarith
            positivity
          linarith
        refine ⟨hd, ?_⟩
        rw [div_eq_div_iff hd h2.ne', e1, e2]; ring
    obtain ⟨hd, hk⟩ := hv
    rw [← hκ] at hk
    have hk0 : 0 < κ := by rw [hk]; positivity
    have hk1 : κ < 1 := by rw [hk, div_lt_one h2]; nlinarith
    refine ⟨fun e => hd (by rw [e]; ring), hk, hk0, hk1, ?_, ?_⟩
    · rw [hk]; field_simp
    · rw [hk]; field_simp; ring

/-- **Theorem `theorem:rationaliso`.** If a triangle of shape `(β, 3α, β)` or
`(α + β, α, α + β)` is tiled by copies of `T`, then `T` is rational, and
`s = (M₁ + M₂)/(M₁ - M₂)` and `s = (M₁ + M₂)/(M₂ - M₁)` respectively. -/
theorem rationaliso {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) (hccw : 0 < D.target.det)
    {M₁ M₂ : ℤ} (h₁ : PhiR (Phi1 (α + β) (baseDir D)) D.target = M₁ * (a + b + c))
    (h₂ : PhiR (Phi2 (α + β) (baseDir D)) D.target = M₂ * (a - b - c)) :
    let s := a / c
    let shape := fun x y z : ℝ =>
      D.target.angleAt 0 = x ∧ D.target.angleAt 1 = y ∧ D.target.angleAt 2 = z
    (shape β (3 * α) β → RationalTile a b c ∧ s = (M₁ + M₂) / (M₁ - M₂)) ∧
    (shape (α + β) α (α + β) → RationalTile a b c ∧ s = (M₁ + M₂) / (M₂ - M₁)) := by
  intro s shape
  have m := M1M2 D hrel hT hns hccw h₁ h₂
  dsimp only at m
  obtain ⟨m1, m2, m3, m4, m5, -, -⟩ := m
  obtain ⟨-, -, -, -, hc, ha, -, ht0, ht1, -, -⟩ := model_facts D hrel hT
  have hst : a / c = 2 * Real.cos (α + β) := by rw [ha]; field_simp
  have hΛ : 0 < Lam D := div_pos (circumdiam_pos _) (circumdiam_pos _)
  rw [hst] at m1 m2 m3 m4 m5
  set t := 2 * Real.cos (α + β)
  have h1p : 0 < 1 + t := by linarith
  have h1m : 0 < 1 - t := by linarith
  have h2 : 0 < 2 - t ^ 2 := by nlinarith
  obtain ⟨-, -, -, -, -, -, hb, -, -, -, -⟩ := model_facts D hrel hT
  simp only [s, hst]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨e1, e2⟩ := m2 h
    have hd : (M₁ : ℝ) - M₂ ≠ 0 := by
      rw [e1, e2]; apply ne_of_gt
      have : 0 < Lam D * (1 - t) * (1 + t) * 2 := by positivity
      nlinarith
    have hs : t = (M₁ + M₂) / (M₁ - M₂) := by rw [eq_div_iff hd, e1, e2]; ring
    exact ⟨rationalTile_of hc ha hb ht0 ht1 (q := (M₁ + M₂) / (M₁ - M₂)) (by rw [hs]; push_cast; rfl),
      hs⟩
  · obtain ⟨e1, e2⟩ := m3 h
    have hd : (M₂ : ℝ) - M₁ ≠ 0 := by
      rw [e1, e2]; apply ne_of_lt
      have : 0 < Lam D / (1 + t) := by positivity
      have : 0 < Lam D / (1 - t) := by positivity
      rw [neg_div]; linarith
    have hs : t = (M₁ + M₂) / (M₂ - M₁) := by rw [eq_div_iff hd, e1, e2]; field_simp; ring
    exact ⟨rationalTile_of hc ha hb ht0 ht1 (q := (M₁ + M₂) / (M₂ - M₁)) (by rw [hs]; push_cast; rfl),
      hs⟩

/-- **Theorem `theorem:shape45`.** Let `ABC` have shape `(α, α + 2β, α)` or `(2α, α, 2β)` and be
tiled by `N` copies of `T`. Then `N + M₁M₂ ≠ 0`, and
`s² = 2(2N + M₁M₂)/(N + M₁M₂)` in the first case, `s² = (M₁ + M₂)²/(2(N + M₁M₂))` in the second.
In either case `s² ∈ ℚ`, hence `s = κ(2 - s²) ∈ ℚ` by `lemma:kappa`, and `T` is rational. -/
theorem shape45 {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) (hccw : 0 < D.target.det)
    {M₁ M₂ : ℤ} (h₁ : PhiR (Phi1 (α + β) (baseDir D)) D.target = M₁ * (a + b + c))
    (h₂ : PhiR (Phi2 (α + β) (baseDir D)) D.target = M₂ * (a - b - c)) :
    let s := a / c
    let shape := fun x y z : ℝ =>
      D.target.angleAt 0 = x ∧ D.target.angleAt 1 = y ∧ D.target.angleAt 2 = z
    (shape α (α + 2 * β) α →
      (N : ℤ) + M₁ * M₂ ≠ 0 ∧ s ^ 2 = 2 * (2 * N + M₁ * M₂) / (N + M₁ * M₂)) ∧
    (shape (2 * α) α (2 * β) →
      (N : ℤ) + M₁ * M₂ ≠ 0 ∧ s ^ 2 = (M₁ + M₂) ^ 2 / (2 * (N + M₁ * M₂))) ∧
    (shape α (α + 2 * β) α ∨ shape (2 * α) α (2 * β) →
      (∃ q : ℚ, s ^ 2 = q) ∧ (∃ q : ℚ, s = q) ∧ RationalTile a b c) := by
  intro s shape
  have m := M1M2 D hrel hT hns hccw h₁ h₂
  dsimp only at m
  obtain ⟨m1, m2, m3, m4, m5, -, -⟩ := m
  obtain ⟨-, -, -, -, hc, ha, -, ht0, ht1, -, -⟩ := model_facts D hrel hT
  have hst : a / c = 2 * Real.cos (α + β) := by rw [ha]; field_simp
  have hΛ : 0 < Lam D := div_pos (circumdiam_pos _) (circumdiam_pos _)
  rw [hst] at m1 m2 m3 m4 m5
  set t := 2 * Real.cos (α + β)
  have h1p : 0 < 1 + t := by linarith
  have h1m : 0 < 1 - t := by linarith
  have h2 : 0 < 2 - t ^ 2 := by nlinarith
  obtain ⟨-, -, -, -, -, -, hb, -, -, -, -⟩ := model_facts D hrel hT
  have ar := shapeareas D hrel hT
  dsimp only at ar
  obtain ⟨-, -, -, a4, a5⟩ := ar
  rw [hst] at a4 a5
  have hΛ2 : Lam D ^ 2 ≠ 0 := by positivity
  have kp := kappa D hrel hT hns hccw h₁ h₂
  dsimp only at kp
  obtain ⟨-, -, -, k45⟩ := kp
  rw [hst] at k45
  simp only [s, hst]
  have case4 : shape α (α + 2 * β) α →
      (N : ℤ) + M₁ * M₂ ≠ 0 ∧ t ^ 2 = 2 * (2 * N + M₁ * M₂) / (N + M₁ * M₂) := by
    intro h
    obtain ⟨e1, e2⟩ := m4 h
    have eN : (N : ℝ) = Lam D ^ 2 * (t ^ 2 * (2 - t ^ 2) / (1 - t ^ 2)) := by
      rw [← a4 h]; field_simp
    have h1t : (1 : ℝ) - t ^ 2 ≠ 0 := by nlinarith
    have hsum : ((N : ℤ) + M₁ * M₂ : ℝ) = -2 * Lam D ^ 2 * t ^ 2 / (1 - t ^ 2) := by
      push_cast; rw [eN, e1, e2]; field_simp; ring
    have hne : ((N : ℤ) + M₁ * M₂ : ℝ) ≠ 0 := by
      rw [hsum]; apply ne_of_lt; apply div_neg_of_neg_of_pos _ (by nlinarith)
      have : 0 < Lam D ^ 2 * t ^ 2 := by positivity
      linarith
    refine ⟨fun e => hne (by exact_mod_cast e), ?_⟩
    have hne' : (N : ℝ) + M₁ * M₂ ≠ 0 := by exact_mod_cast hne
    rw [eq_div_iff hne', eN, e1, e2]; field_simp; ring
  have case5 : shape (2 * α) α (2 * β) →
      (N : ℤ) + M₁ * M₂ ≠ 0 ∧ t ^ 2 = (M₁ + M₂) ^ 2 / (2 * (N + M₁ * M₂)) := by
    intro h
    obtain ⟨e1, e2⟩ := m5 h
    have eN : (N : ℝ) = Lam D ^ 2 * (t ^ 2 * (2 - t ^ 2) * (3 - t ^ 2)) := by
      rw [← a5 h]; field_simp
    have hsum : ((N : ℤ) + M₁ * M₂ : ℝ) = 2 * Lam D ^ 2 * t ^ 2 := by
      push_cast; rw [eN, e1, e2]; ring
    have hne : ((N : ℤ) + M₁ * M₂ : ℝ) ≠ 0 := by
      rw [hsum]; apply ne_of_gt
      positivity
    refine ⟨fun e => hne (by exact_mod_cast e), ?_⟩
    have hne' : (N : ℝ) + M₁ * M₂ ≠ 0 := by exact_mod_cast hne
    rw [eq_div_iff (by positivity), e1, e2, eN]; ring
  refine ⟨case4, case5, fun h => ?_⟩
  have hsq : ∃ q : ℚ, t ^ 2 = q := by
    rcases h with h | h
    · obtain ⟨-, e⟩ := case4 h
      exact ⟨2 * (2 * N + M₁ * M₂) / (N + M₁ * M₂), by rw [e]; push_cast; rfl⟩
    · obtain ⟨-, e⟩ := case5 h
      exact ⟨(M₁ + M₂) ^ 2 / (2 * (N + M₁ * M₂)), by rw [e]; push_cast; rfl⟩
  obtain ⟨q, hq⟩ := hsq
  obtain ⟨-, -, -, -, hk, -⟩ := k45 h
  have ht : t = (((M₁ + M₂) / (M₂ - M₁) * (2 - q) : ℚ) : ℝ) := by
    rw [hk, hq]; push_cast; rfl
  exact ⟨⟨q, hq⟩, ⟨_, ht⟩, rationalTile_of hc ha hb ht0 ht1 ht⟩

end TriangleTiling.ThreeAlpha
