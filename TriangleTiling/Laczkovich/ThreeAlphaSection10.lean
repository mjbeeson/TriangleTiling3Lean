/-
The `d` matrix of the triangle with angles `(2α, β, α + β)` (M. Beeson, *Triangle tiling: the case
3α + 2β = π*, arXiv 1206.2229v4): `lemma:dmatrix`, `lemma:52`, `lemma:XYZ`, `lemma:n<K`,
`lemma:X=M(b+c)`, `lemma:jmk`, `lemma:congruences`, `corollary:nokt`.

Statements not yet checked by Beeson. Conventions as in the paper: the angle at `A` (`target.pts 0`)
is `2α`, at `B` is `β`, at `C` is `α + β`; `X, Y, Z` are the sides opposite `A, B, C`; the rows of
the `d` matrix are `(p, d, e)`, `(g, n, f)`, `(h, ℓ, r)` (`dEntry D j θ`, `j = 0, 1, 2`,
`θ = α, β, γ`). The scaling factor `μ` is `Lam D`, the ratio of the circumdiameters. TeX labels with
characters Lean does not allow become `lemma52`, `nltK`, `XeqMbc`.
-/
import TriangleTiling.Laczkovich.ThreeAlphaNo28
import TriangleTiling.ThreeAlpha.DMatrix
import TriangleTiling.TwoCs.Pigeonhole

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.BeesonColoring Set
open Erdos634.Draft.LaczFormal (TileAngles)

variable {N : ℕ} (D : CongruentDissection N)

/-- The sides and area of the triquadratic triangle, by the scale `Λ`. -/
theorem tq_scale {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) :
    let s := 2 * Real.sin (α / 2)
    a = s * c ∧ b = (1 - s ^ 2) * c ∧ 0 < s ∧ s < 1 ∧ 0 < c ∧ 0 < Lam D ∧
      D.target.oppLen 0 = Lam D * ((2 - s ^ 2) * a) ∧ D.target.oppLen 1 = Lam D * b ∧
      D.target.oppLen 2 = Lam D * c ∧ (N : ℝ) = Lam D ^ 2 * (2 - s ^ 2) := by
  intro s
  obtain ⟨hα, hβ, -, hS, hc, ha, hb, ht0, ht1, -, -⟩ := model_facts D hrel hT
  have hts : 2 * Real.cos (α + β) = s := by
    simp only [s]; rw [show α + β = Real.pi / 2 - α / 2 by linarith, Real.cos_pi_div_two_sub]
  rw [hts] at ha hb ht0 ht1
  have hΛ : 0 < Lam D := div_pos (circumdiam_pos _) (circumdiam_pos _)
  have ar := (shapeareas D hrel hT).1 hshape
  have hst : a / c = s := by rw [ha]; field_simp
  rw [hst, div_eq_iff (by positivity)] at ar
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨-, r2, -, r4, r5, -, -, -⟩ := r
  rw [hts] at r2 r5
  rw [div_eq_iff hS.ne'] at r2 r4 r5
  have s0 := target_side D hrel hT 0
  have s1 := target_side D hrel hT 1
  have s2 := target_side D hrel hT 2
  rw [hshape.1, r5] at s0
  rw [hshape.2.1, r2] at s1
  rw [hshape.2.2, r4] at s2
  have hS' := hS.ne'
  refine ⟨ha, hb, ht0, ht1, hc, hΛ, ?_, ?_, ?_, by rw [ar]; ring⟩
  · rw [s0, ha]; field_simp
  · rw [s1, hb]; field_simp
  · rw [s2]; field_simp

/-- **Lemma `lemma:dmatrix`.** Let the angles of `ABC` be `(2α, β, α + β)`. Let `X, Y, Z` be the
lengths of `BC, AC, AB`, and `s = 2 sin (α/2)`. Then for a suitable scaling factor `μ`,
`(X, Y, Z) = d (a, b, c) = μ ((2 - s²) a, b, c)`. -/
theorem dmatrix {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) :
    let s := 2 * Real.sin (α / 2)
    (∀ j, D.target.oppLen j = dEntry D j α * a + dEntry D j β * b + dEntry D j γ * c) ∧
      ∃ μ > 0, D.target.oppLen 0 = μ * ((2 - s ^ 2) * a) ∧ D.target.oppLen 1 = μ * b ∧
        D.target.oppLen 2 = μ * c := by
  intro s
  obtain ⟨-, -, hγ, -⟩ := model_facts D hrel hT
  have hns := not_similar_of_alpha_beta D hrel hT hshape.2.2
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  have hirr := (angles D hrel hT' hns).1
  have h := threeAlphaData_of_sides D hrel hT
  obtain ⟨-, -, -, -, -, hΛ, hX, hY, hZ, -⟩ := tq_scale D hrel hT hshape
  refine ⟨fun j => hγ ▸ dmatrix_row D hirr hrel h j, Lam D, hΛ, hX, hY, hZ⟩

/-- The coloring equation for this shape: `M = Λ s`, with the facts of `tq_scale`. -/
theorem tq_coloring {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    ((∑ i, ε i : ℤ) : ℝ) = Lam D * (2 * Real.sin (α / 2)) := by
  obtain ⟨hα, hβ, hγ, -⟩ := model_facts D hrel hT
  have hns := not_similar_of_alpha_beta D hrel hT hshape.2.2
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  have hirr := (angles D hrel hT' hns).1
  have h := threeAlphaData_of_sides D hrel hT
  have hns3 := not_triple3 D hrel hT' hns
  obtain ⟨-, -, t0⟩ := corner_counts D hirr hrel h hns3 0 (p := 2) (q := 0)
    (by rw [hshape.1]; push_cast; ring)
  obtain ⟨-, -, t2⟩ := corner_counts D hirr hrel h hns3 2 (p := 1) (q := 1)
    (by rw [hshape.2.2]; push_cast; ring)
  have hcol := (coloring D hrel hT hns).2 (by rw [t0, t2]) ε i₀ hε hi₀ hb
  have hM := hcol.2 (by
    rintro (⟨h0, -⟩ | ⟨-, h2⟩)
    · rw [hshape.1] at h0; linarith
    · rw [hshape.2.2] at h2; linarith)
  obtain ⟨ha, hb', hs0, hs1, hc, hΛ, hX, hY, hZ, -⟩ := tq_scale D hrel hT hshape
  simp only at hM
  rw [hX, hY, hZ, hb', ha] at hM
  set s := 2 * Real.sin (α / 2)
  have hpos : 0 < c * (2 + s - s ^ 2) := by
    have : 0 < 2 + s - s ^ 2 := by nlinarith
    positivity
  have : (((∑ i, ε i : ℤ) : ℝ) - Lam D * s) * (c * (2 + s - s ^ 2)) = 0 := by
    linear_combination hM
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · linarith

/-- **Lemma `lemma:52`.** Let `3α + 2β = π` and assume triangle `ABC` has angles `(2α, β, α + β)`
and is `N`-tiled by a tile with angles `α` and `β`. Let the tiles be assigned signs (colors) in
accordance with `lemma:signedtiles` (a tile at `B`, with an edge on `AB`, black). Let
`s = 2 sin (α/2)` and let `M` be the number of black tiles minus the number of white tiles. Then
`M > 0`, `μ = M/s`, and `s² = 2M²/(M² + N)`. (`μ` is `Lam D`.) -/
theorem lemma52 {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    let s := 2 * Real.sin (α / 2)
    let M : ℤ := ∑ i, ε i
    0 < M ∧ Lam D = M / s ∧ s ^ 2 = 2 * (M : ℝ) ^ 2 / ((M : ℝ) ^ 2 + N) := by
  intro s M
  have hM := tq_coloring D hrel hT hshape hε hi₀ hb
  obtain ⟨-, -, hs0, hs1, -, hΛ, -, -, -, hN⟩ := tq_scale D hrel hT hshape
  have hMpos : (0 : ℝ) < M := by rw [hM]; positivity
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hsin : Real.sin (α / 2) ≠ 0 := fun h => hsne (by simp only [s, h, mul_zero])
  refine ⟨by exact_mod_cast hMpos, by rw [hM]; simp only [s]; field_simp, ?_⟩
  rw [eq_div_iff (by positivity), hN, hM]
  simp only [s]
  ring

/-- **Lemma `lemma:XYZ`.** Assume triangle `ABC` has angles `(2α, β, α + β)`, there is an
`N`-tiling, and `N + M² = 2K²` where `K = M/s`. Then for some `λ > 0`,
`(a, b, c) = λ (M, N/K - K, K)`, `(X, Y, Z) = λ (MN/K, N - K², K²)`, and the `d`-matrix equation
takes the form `MN/K = pM + d(N/K - K) + eK`, `N - K² = gM + n(N/K - K) + fK`,
`K² = hM + ℓ(N/K - K) + rK`. (`M` is the coloring number of `lemma:52`.) -/
theorem XYZ {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    let s := 2 * Real.sin (α / 2)
    let M : ℝ := ((∑ i, ε i : ℤ) : ℝ)
    let K := M / s
    (N : ℝ) + M ^ 2 = 2 * K ^ 2 →
    ∃ l > (0 : ℝ), (a = l * M ∧ b = l * (N / K - K) ∧ c = l * K) ∧
      (D.target.oppLen 0 = l * (M * N / K) ∧ D.target.oppLen 1 = l * (N - K ^ 2) ∧
        D.target.oppLen 2 = l * K ^ 2) ∧
      (M * N / K = dEntry D 0 α * M + dEntry D 0 β * (N / K - K) + dEntry D 0 γ * K ∧
        N - K ^ 2 = dEntry D 1 α * M + dEntry D 1 β * (N / K - K) + dEntry D 1 γ * K ∧
        K ^ 2 = dEntry D 2 α * M + dEntry D 2 β * (N / K - K) + dEntry D 2 γ * K) := by
  intro s M K hK
  have hM := tq_coloring D hrel hT hshape hε hi₀ hb
  obtain ⟨ha, hb', hs0, hs1, hc, hΛ, hX, hY, hZ, hN⟩ := tq_scale D hrel hT hshape
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hsin : Real.sin (α / 2) ≠ 0 := fun h => hsne (by simp only [s, h, mul_zero])
  have hKΛ : K = Lam D := by simp only [K, M]; rw [hM]; simp only [s]; field_simp
  have hK0 : 0 < K := hKΛ ▸ hΛ
  have hMs : M = K * s := by simp only [K]; field_simp
  set l := c / K
  have hl : 0 < l := by positivity
  have hcl : c = l * K := by simp only [l]; field_simp
  have hNK : (N : ℝ) / K - K = K * (1 - s ^ 2) := by
    rw [hN, ← hKΛ]; field_simp; ring
  have hrows := (dmatrix D hrel hT hshape).1
  -- Everything in terms of `l, K, s`.
  have ea : a = l * M := by rw [ha, hcl, hMs]; ring
  have eb : b = l * (N / K - K) := by rw [hb', hcl, hNK]; ring
  have eX : D.target.oppLen 0 = l * (M * N / K) := by
    rw [hX, ← hKΛ, ha, hcl, hMs, hN, ← hKΛ]; field_simp; ring
  have eY : D.target.oppLen 1 = l * (N - K ^ 2) := by
    rw [hY, ← hKΛ, hb', hcl, hN, ← hKΛ]; ring
  have eZ : D.target.oppLen 2 = l * K ^ 2 := by rw [hZ, ← hKΛ, hcl]; ring
  refine ⟨l, hl, ⟨ea, eb, hcl⟩, ⟨eX, eY, eZ⟩, ?_, ?_, ?_⟩
  · have r := hrows 0
    rw [eX, ea, eb, hcl] at r
    apply mul_left_cancel₀ hl.ne'
    linear_combination r
  · have r := hrows 1
    rw [eY, ea, eb, hcl] at r
    apply mul_left_cancel₀ hl.ne'
    linear_combination r
  · have r := hrows 2
    rw [eZ, ea, eb, hcl] at r
    apply mul_left_cancel₀ hl.ne'
    linear_combination r

-- `N + M² = 2K²` is part of the printed hypotheses; the identity does not need it.
set_option linter.unusedVariables false in
/-- **Lemma `lemma:X=M(b+c)`.** Assume triangle `ABC` has angles `(2α, β, α + β)`, there is an
`N`-tiling, and `N + M² = 2K²`. Then the length of `BC` is `X = M(b + c)`. (`M` is the coloring
number of `lemma:52`, `K = M/s`.) -/
theorem XeqMbc {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    let M : ℝ := ((∑ i, ε i : ℤ) : ℝ)
    let K := M / (2 * Real.sin (α / 2))
    (N : ℝ) + M ^ 2 = 2 * K ^ 2 → D.target.oppLen 0 = M * (b + c) := by
  intro M K hK
  have hM := tq_coloring D hrel hT hshape hε hi₀ hb
  obtain ⟨ha, hb', -, -, -, -, hX, -, -, -⟩ := tq_scale D hrel hT hshape
  simp only [M]
  rw [hX, hM, ha, hb']
  ring

/-- With `M, K` satisfying the tiling equation and `s = M/K`, the scale is `Λ = K`. -/
theorem lam_eq_K {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β)
    {M K : ℕ} (hK : 0 < K) (hMK : M ^ 2 + N = 2 * K ^ 2) (hs : 2 * Real.sin (α / 2) = M / K) :
    Lam D = K := by
  obtain ⟨-, -, -, -, -, hΛ, -, -, -, hN⟩ := tq_scale D hrel hT hshape
  rw [hs] at hN
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hMKR : (M : ℝ) ^ 2 + N = 2 * K ^ 2 := by exact_mod_cast hMK
  have hN0 : (0 : ℝ) < N := by
    have h1 : (M : ℝ) / K < 1 := by
      obtain ⟨-, -, -, h1, -⟩ := tq_scale D hrel hT hshape
      rw [hs] at h1; exact h1
    rw [div_lt_one hKR] at h1
    nlinarith
  have h2 : (2 : ℝ) - ((M : ℝ) / K) ^ 2 = N / (K : ℝ) ^ 2 := by field_simp; linarith
  rw [h2] at hN
  have : (Lam D) ^ 2 = (K : ℝ) ^ 2 := by
    field_simp at hN
    linarith
  nlinarith [sq_nonneg (Lam D - K), sq_nonneg (Lam D + K)]

/-- The side `AC` (opposite `B`) carries a `c` edge: `f ≥ 1`. -/
theorem f_pos {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) :
    1 ≤ dEntry D 1 γ := by
  classical
  obtain ⟨hα, hβ, hγ, -, hc, ha, hb, ht0, ht1, -, -⟩ := model_facts D hrel hT
  have hns := not_similar_of_alpha_beta D hrel hT hshape.2.2
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  have hirr := (angles D hrel hT' hns).1
  have h := threeAlphaData_of_sides D hrel hT
  by_contra hf
  push Not at hf
  have hf0 : dEntry D 1 γ = 0 := by omega
  -- No `c` edge on `AC`, so by `lemma:pigeonhole` a `γ` at `A` or `C`.
  obtain ⟨i, l, hl, hlγ⟩ := pigeonhole D hT (by rw [hγ]; linarith) 1 (by
    intro i m hm hlen
    have hmem : (i, m) ∈ (sideEdges D 1).filter (edgeType D γ) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩, ?_⟩
      -- an edge of length `c` is opposite the angle `γ`
      obtain ⟨ρ, h0, l0, h1, l1, h2, l2⟩ := tile_threeAlpha D h i
      have hd : dist ((D.tile i).pts m) ((D.tile i).pts (m + 1)) = (D.tile i).oppLen (m + 2) := by
        unfold Tri.oppLen
        rw [(by decide : ∀ x : Fin 3, x + 2 + 1 = x) m,
          (by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) m]
      unfold edgeType
      rw [localAngle_pts, hγ]
      obtain ⟨u, hu⟩ := ρ.surjective (m + 2)
      rw [hd, ← hu] at hlen
      rw [← hu]
      fin_cases u
      · exfalso; simp only [Fin.zero_eta] at hlen; rw [l0, ha] at hlen
        have : (1 - 2 * Real.cos (α + β)) * c = 0 := by linarith
        rcases mul_eq_zero.mp this with h' | h' <;> linarith
      · exfalso; simp only [Fin.mk_one] at hlen; rw [l1, hb] at hlen
        have : (2 * Real.cos (α + β)) ^ 2 * c = 0 := by linarith
        rcases mul_eq_zero.mp this with h' | h'
        · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h'; linarith
        · linarith
      · exact h2
    have := Finset.card_pos.mpr ⟨_, hmem⟩
    unfold dEntry at hf0
    omega)
  have := (nogamma D hrel hT' hns).1
  rcases hl with hl | hl
  · exact this _ i l hl hlγ
  · exact this _ i l hl hlγ

/-- **Lemma `lemma:n<K`.** Suppose given an `N`-tiling of a triangle `ABC` with angles
`(2α, β, α + β)`, and integers `M, K` satisfying the tiling equation with `s = M/K`. Then `n < K`,
where `n` is the number of `b` edges on the side `AC` of `ABC` opposite the `β` angle. -/
theorem nltK {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β)
    {M K : ℕ} (hM : 0 < M) (hK : 0 < K) (hMK : M ^ 2 + N = 2 * K ^ 2)
    (hs : 2 * Real.sin (α / 2) = M / K) : dEntry D 1 β < K := by
  have hΛK := lam_eq_K D hrel hT hshape hK hMK hs
  obtain ⟨ha, hb, hs0, hs1, hc, -, -, hY, -, -⟩ := tq_scale D hrel hT hshape
  have hrow := (dmatrix D hrel hT hshape).1 1
  have hf := f_pos D hrel hT hshape
  rw [hY, hΛK] at hrow
  have hb0 : 0 < b := by rw [hb]; have : 0 < 1 - (2 * Real.sin (α / 2)) ^ 2 := by nlinarith
                         positivity
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hfR : (1 : ℝ) ≤ dEntry D 1 γ := by exact_mod_cast hf
  have hgR : (0 : ℝ) ≤ dEntry D 1 α := Nat.cast_nonneg _
  have : ((dEntry D 1 β : ℕ) : ℝ) * b < K * b := by nlinarith
  have := lt_of_mul_lt_mul_right this hb0.le
  exact_mod_cast this

/-- **Lemma `lemma:jmk`.** Assume triangle `ABC` has angles `(2α, β, α + β)` and there is an
`N`-tiling, and let `M, K` be as in `theorem:tilingequation`, so that `M² + N = 2K²` and
`s = M/K`. Let the tile have integer sides `(a, b, c)` with no common factor; with `m, k` as in
`lemma:gsquare`, `(a, b, c) = (mk, k² - m², k²)` and `a/c = m/k` in lowest terms. Put
`j = gcd(M, K)`. Then `M = jm`, `K = jk`, `N = j²(2k² - m²)`, `X = M(b + c)`, `Y = Kb`, `Z = Kc`.
Moreover `K ∣ M²` if and only if `k ∣ j`. -/
theorem jmk {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β)
    {M K : ℕ} (hM : 0 < M) (hK : 0 < K) (hMK : M ^ 2 + N = 2 * K ^ 2)
    (hs : 2 * Real.sin (α / 2) = M / K)
    {a' b' c' : ℕ} (hint : a = a' ∧ b = b' ∧ c = c') (hprim : Nat.gcd (Nat.gcd a' b') c' = 1) :
    ∃ m k : ℕ, Nat.Coprime m k ∧ m < k ∧ a' = m * k ∧ b' = k ^ 2 - m ^ 2 ∧ c' = k ^ 2 ∧
      a / c = m / k ∧
      M = Nat.gcd M K * m ∧ K = Nat.gcd M K * k ∧
      N = Nat.gcd M K ^ 2 * (2 * k ^ 2 - m ^ 2) ∧
      D.target.oppLen 0 = M * (b + c) ∧ D.target.oppLen 1 = K * b ∧ D.target.oppLen 2 = K * c ∧
      (K ∣ M ^ 2 ↔ k ∣ Nat.gcd M K) := by
  have hΛK := lam_eq_K D hrel hT hshape hK hMK hs
  obtain ⟨ha, hb, hs0, hs1, hc, -, hX, hY, hZ, -⟩ := tq_scale D hrel hT hshape
  set j := Nat.gcd M K
  have hj : 0 < j := Nat.gcd_pos_of_pos_left _ hM
  set m := M / j
  set k := K / j
  have hMj : M = j * m := (Nat.mul_div_cancel' (Nat.gcd_dvd_left M K)).symm
  have hKj : K = j * k := (Nat.mul_div_cancel' (Nat.gcd_dvd_right M K)).symm
  have hcop : Nat.Coprime m k := Nat.coprime_div_gcd_div_gcd hj
  have hk : 0 < k := Nat.div_pos (Nat.le_of_dvd hK (Nat.gcd_dvd_right M K)) hj
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsmk : 2 * Real.sin (α / 2) = m / k := by
    rw [hs, hMj, hKj]; push_cast; field_simp
  obtain ⟨ea, eb, ec⟩ := hint
  have hc0 : 0 < c' := by
    have : (0 : ℝ) < c' := ec ▸ hc
    exact_mod_cast this
  have hb0 : 0 < b' := by
    have : (0 : ℝ) < b' := by
      rw [← eb, hb]
      have : 0 < 1 - (2 * Real.sin (α / 2)) ^ 2 := by nlinarith
      positivity
    exact_mod_cast this
  have hrel' : a' ^ 2 + b' * c' = c' ^ 2 := by
    have : ((a' ^ 2 + b' * c' : ℕ) : ℝ) = ((c' ^ 2 : ℕ) : ℝ) := by
      push_cast; rw [← ea, ← eb, ← ec, ha, hb]; ring
    exact_mod_cast this
  have hratio : a' * k = m * c' := by
    have : ((a' * k : ℕ) : ℝ) = ((m * c' : ℕ) : ℝ) := by
      push_cast; rw [← ea, ← ec, ha, hsmk]; field_simp
    exact_mod_cast this
  obtain ⟨hae, hbe, hce, -, -, hmk⟩ := gsquare_arith a' b' c' m k hb0 hc0 hprim hrel' hcop hk hratio
  refine ⟨m, k, hcop, hmk, hae, hbe, hce, ?_, hMj, hKj, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha, hsmk]; field_simp
  · -- `N = 2K² - M²`
    have hle : m ^ 2 ≤ 2 * k ^ 2 := by nlinarith
    rw [hMj, hKj] at hMK
    have : N = 2 * (j * k) ^ 2 - (j * m) ^ 2 := by omega
    rw [this, Nat.mul_sub, mul_pow, mul_pow]; ring_nf
  · rw [hX, hΛK, ha, hb, hs]
    have hN : (N : ℝ) = 2 * K ^ 2 - M ^ 2 := by
      have : ((M ^ 2 + N : ℕ) : ℝ) = ((2 * K ^ 2 : ℕ) : ℝ) := by exact_mod_cast hMK
      push_cast at this; linarith
    field_simp
    ring
  · rw [hY, hΛK]
  · rw [hZ, hΛK]
  · -- `jk ∣ j²m² ↔ k ∣ j m² ↔ k ∣ j`.
    rw [hMj, hKj, mul_pow]
    constructor
    · intro hd
      have h1 : k ∣ j * m ^ 2 := by
        have : j * k ∣ j * (j * m ^ 2) := by rw [show j * (j * m ^ 2) = j ^ 2 * m ^ 2 by ring]; exact hd
        exact Nat.dvd_of_mul_dvd_mul_left hj this
      exact (Nat.Coprime.pow_right 2 hcop.symm).dvd_of_dvd_mul_right h1
    · intro hd
      obtain ⟨t, ht⟩ := hd
      exact ⟨t * m ^ 2, by rw [ht]; ring⟩

/-- **Lemma `lemma:congruences`.** Under the hypotheses and notation of `lemma:jmk`, the entries of
the `d` matrix satisfy `k ∣ n`, `k ∣ ℓ`, `d ≡ jm (mod k)`, where `n` is the number of `b` edges on
`AC`, `ℓ` the number of `b` edges on `AB`, and `d` the number of `b` edges on `BC`. -/
theorem congruences {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β)
    {M K : ℕ} (hM : 0 < M) (hK : 0 < K) (hMK : M ^ 2 + N = 2 * K ^ 2)
    (hs : 2 * Real.sin (α / 2) = M / K)
    {a' b' c' : ℕ} (hint : a = a' ∧ b = b' ∧ c = c') (hprim : Nat.gcd (Nat.gcd a' b') c' = 1)
    {m k : ℕ} (hmk : Nat.Coprime m k) (hmk' : m < k) (ha : a' = m * k) (hb : b' = k ^ 2 - m ^ 2)
    (hc : c' = k ^ 2) (hMj : M = Nat.gcd M K * m) (hKj : K = Nat.gcd M K * k) :
    k ∣ dEntry D 1 β ∧ k ∣ dEntry D 2 β ∧
      (dEntry D 0 β : ℤ) ≡ Nat.gcd M K * m [ZMOD k] := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hX, hY, hZ, -⟩ :=
    jmk D hrel hT hshape hM hK hMK hs hint hprim
  set j := Nat.gcd M K
  have hrows := (dmatrix D hrel hT hshape).1
  obtain ⟨ea, eb, ec⟩ := hint
  have hle : m ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left hmk'.le 2
  have hbR : (b : ℝ) = (k : ℝ) ^ 2 - m ^ 2 := by rw [eb, hb]; push_cast [hle]; ring
  have haR : (a : ℝ) = m * k := by rw [ea, ha]; push_cast; ring
  have hcR : (c : ℝ) = k ^ 2 := by rw [ec, hc]; push_cast; ring
  obtain ⟨-, -, hγ, -⟩ := model_facts D hrel hT
  -- The three rows, as integer equations.
  have r1 : ((j * k : ℤ)) * ((k : ℤ) ^ 2 - m ^ 2) = dEntry D 1 α * (m * k) +
      dEntry D 1 β * ((k : ℤ) ^ 2 - m ^ 2) + dEntry D 1 γ * (k : ℤ) ^ 2 := by
    have h1 := hrows 1
    rw [hY, hKj, haR, hbR, hcR] at h1
    push_cast at h1
    exact_mod_cast (by push_cast; linarith : ((j * k : ℤ) : ℝ) * ((k : ℝ) ^ 2 - m ^ 2) =
      (dEntry D 1 α : ℝ) * (m * k) + dEntry D 1 β * ((k : ℝ) ^ 2 - m ^ 2) +
        dEntry D 1 γ * (k : ℝ) ^ 2)
  have r2 : ((j * k : ℤ)) * (k : ℤ) ^ 2 = dEntry D 2 α * (m * k) +
      dEntry D 2 β * ((k : ℤ) ^ 2 - m ^ 2) + dEntry D 2 γ * (k : ℤ) ^ 2 := by
    have h1 := hrows 2
    rw [hZ, hKj, haR, hbR, hcR] at h1
    push_cast at h1
    exact_mod_cast (by push_cast; linarith : ((j * k : ℤ) : ℝ) * (k : ℝ) ^ 2 =
      (dEntry D 2 α : ℝ) * (m * k) + dEntry D 2 β * ((k : ℝ) ^ 2 - m ^ 2) +
        dEntry D 2 γ * (k : ℝ) ^ 2)
  have r0 : ((j * m : ℤ)) * (2 * (k : ℤ) ^ 2 - m ^ 2) = dEntry D 0 α * (m * k) +
      dEntry D 0 β * ((k : ℤ) ^ 2 - m ^ 2) + dEntry D 0 γ * (k : ℤ) ^ 2 := by
    have h1 := hrows 0
    rw [hX, hMj, hbR, haR, hcR] at h1
    push_cast at h1
    exact_mod_cast (by push_cast; linarith : ((j * m : ℤ) : ℝ) * (2 * (k : ℝ) ^ 2 - m ^ 2) =
      (dEntry D 0 α : ℝ) * (m * k) + dEntry D 0 β * ((k : ℝ) ^ 2 - m ^ 2) +
        dEntry D 0 γ * (k : ℝ) ^ 2)
  have hcopZ : IsCoprime (k : ℤ) ((m : ℤ) ^ 2) :=
    (Nat.isCoprime_iff_coprime.mpr hmk.symm).pow_right
  refine ⟨?_, ?_, ?_⟩
  · have : (k : ℤ) ∣ dEntry D 1 β * (m : ℤ) ^ 2 :=
      ⟨dEntry D 1 β * k - j * (k ^ 2 - m ^ 2) + dEntry D 1 α * m + dEntry D 1 γ * k, by
        linear_combination r1⟩
    exact_mod_cast hcopZ.dvd_of_dvd_mul_right this
  · have : (k : ℤ) ∣ dEntry D 2 β * (m : ℤ) ^ 2 :=
      ⟨dEntry D 2 β * k - j * k ^ 2 + dEntry D 2 α * m + dEntry D 2 γ * k, by
        linear_combination r2⟩
    exact_mod_cast hcopZ.dvd_of_dvd_mul_right this
  · rw [Int.modEq_iff_dvd]
    have : (k : ℤ) ∣ ((j : ℤ) * m - dEntry D 0 β) * (m : ℤ) ^ 2 :=
      ⟨2 * j * m * k - dEntry D 0 α * m - dEntry D 0 β * k - dEntry D 0 γ * k, by
        linear_combination -r0⟩
    exact hcopZ.dvd_of_dvd_mul_right this

/-- **Corollary `corollary:nokt`.** Under the hypotheses of `lemma:jmk`, `n = kt` for some integer
`t` with `0 ≤ t < j`. In particular, if `gcd(M, K) = 1` then `n = 0`: there are no `b` edges at
all on the side `AC`. -/
theorem nokt {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β)
    {M K : ℕ} (hM : 0 < M) (hK : 0 < K) (hMK : M ^ 2 + N = 2 * K ^ 2)
    (hs : 2 * Real.sin (α / 2) = M / K)
    {a' b' c' : ℕ} (hint : a = a' ∧ b = b' ∧ c = c') (hprim : Nat.gcd (Nat.gcd a' b') c' = 1)
    {m k : ℕ} (hmk : Nat.Coprime m k) (hmk' : m < k) (ha : a' = m * k) (hb : b' = k ^ 2 - m ^ 2)
    (hc : c' = k ^ 2) (hMj : M = Nat.gcd M K * m) (hKj : K = Nat.gcd M K * k) :
    ∃ t : ℕ, dEntry D 1 β = k * t ∧ t < Nat.gcd M K ∧ (Nat.gcd M K = 1 → dEntry D 1 β = 0) := by
  obtain ⟨⟨t, ht⟩, -, -⟩ := congruences D hrel hT hshape hM hK hMK hs hint hprim hmk hmk' ha hb hc
    hMj hKj
  have hn := nltK D hrel hT hshape hM hK hMK hs
  have hk : 0 < k := by omega
  have htj : t < Nat.gcd M K := by
    rw [ht, hKj] at hn
    by_contra h
    push Not at h
    have := Nat.mul_le_mul_left k h
    rw [mul_comm k (Nat.gcd M K)] at this
    omega
  refine ⟨t, ht, htj, fun h1 => ?_⟩
  rw [h1] at htj
  rw [ht, show t = 0 by omega, mul_zero]

end TriangleTiling.ThreeAlpha
