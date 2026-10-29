/-
`corollary:isoscelesalphaall` (M. Beeson, *Triangle tiling: the case 3α + 2β = π*, arXiv
1206.2229v4): a tiling of an isosceles triangle with base angles `α`, glued from a tiling of the
isosceles triangle with base angles `α + β` (subdivided by `c`) and a quadratic tiling of a triangle
similar to the tile.

Statement not yet checked by Beeson. The gluing uses Bonfioli's `fan_cover`, `fan_disjoint`,
`unionCongruentDissection` (Erdos634, UNAUDITED).
-/
import TriangleTiling.Laczkovich.ThreeAlphaIsoExist
import TriangleTiling.Laczkovich.ThreeAlphaIsoBetaExist
import TriangleTiling.Laczkovich.ThreeAlphaSecondExist
import TriangleTiling.Laczkovich.ThreeAlphaIsoAB2
import Erdos634.Draft.CVCCevianCut

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.CVCCevianCut (cr triOf carrier_triOf cr_pts_ne_zero fan_cover fan_disjoint
  dist_of_sqd sqd_of_dist range_three)

variable {N : ℕ}

/-- The legs of a tiled isosceles triangle with base angles `α + β`, tile `(a, b, c)` integer with no
common factor, have integer length `M(a + c)`. -/
theorem iso_leg_nat (D : CongruentDissection N) {α β γ : ℝ} {a b c : ℕ}
    (hrel : 3 * α + 2 * β = Real.pi) (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β)
    (hprim : Nat.gcd (Nat.gcd a b) c = 1) :
    ∃ L : ℕ, 0 < L ∧ D.target.oppLen 0 = L ∧ D.target.oppLen 2 = L := by
  obtain ⟨i₀, hi₀⟩ := exists_atB_onAB D
  have hat : TileAt D 1 i₀ := by obtain ⟨l, -, -, hl, -⟩ := hi₀; exact ⟨l, hl⟩
  have hns := not_similar_of_alpha_beta D hrel hT hshape.1
  have hT' : Erdos634.Draft.LaczFormal.TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT; exact ⟨σ, h0, h1, h2⟩
  obtain ⟨ε, hε, hb1⟩ := signedtiles D hrel hT' hns hat
  obtain ⟨hΛ, -⟩ := mu D hrel hT hshape ⟨rfl, rfl, rfl⟩ hprim hε hi₀ hb1
  obtain ⟨o0, -, o2, hΛp⟩ := iso_scale D hrel hT hshape
  obtain ⟨-, -, -, -, hc, -⟩ := model_facts D hrel hT
  set M : ℤ := ∑ i, ε i
  have hLr : D.target.oppLen 0 = M * ((a : ℝ) + c) := by
    rw [o0, hΛ]; field_simp; ring
  have hpos : (0 : ℝ) < M * ((a : ℝ) + c) := by rw [← hLr]; exact oppLen_pos _ _
  have hM : 0 < M := by
    have : (0 : ℝ) < M := pos_of_mul_pos_left hpos (by positivity)
    exact_mod_cast this
  have hMn : ((M.toNat : ℕ) : ℝ) = (M : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hM.le
  refine ⟨M.toNat * (a + c), ?_, ?_, ?_⟩
  · have : 0 < a + c := by have : (0 : ℝ) < c := hc; exact_mod_cast (by positivity : (0 : ℝ) < (a : ℝ) + c)
    exact Nat.mul_pos (by omega) this
  · rw [hLr]; push_cast; rw [hMn]
  · rw [o2, ← o0, hLr]; push_cast; rw [hMn]

theorem pts_eq_vec (T : Erdos634.Geometry.Tri) : T.pts = ![T.pts 0, T.pts 1, T.pts 2] := by
  funext k; fin_cases k <;> rfl

theorem carrier_eq_hull (T : Erdos634.Geometry.Tri) : T.carrier = convexHull ℝ {T.pts 0, T.pts 1, T.pts 2} := by
  unfold Tri.carrier; rw [pts_eq_vec T, range_three]; rfl

/-- **The gluing.** If the isosceles triangle with base angles `α + β` and legs `L` is
`N₁`-tiled by the integer tile `(a, b, c)`, then an isosceles triangle with base angles `α` is
`(L² + c²N₁)`-tiled by it. -/
theorem iso_alpha_glue {N₁ : ℕ} (D₁ : CongruentDissection N₁) {α β : ℝ} {a b c : ℕ}
    (hrel : 3 * α + 2 * β = Real.pi) (hT : TileSides D₁ α β (2 * α + β) a b c)
    (hshape : D₁.target.angleAt 0 = α + β ∧ D₁.target.angleAt 1 = α ∧ D₁.target.angleAt 2 = α + β)
    {L : ℕ} (hL : 0 < L) (hleg0 : D₁.target.oppLen 0 = L) (hleg2 : D₁.target.oppLen 2 = L) :
    ∃ D : CongruentDissection (L * L * 1 + c * c * N₁), TileSides D α β (2 * α + β) a b c ∧
      D.target.angleAt 0 = α ∧ D.target.angleAt 2 = α := by
  obtain ⟨hα, hβ, -, -, hcr, ha, hb, ht0, ht1, -⟩ := model_facts D₁ hrel hT
  set t := 2 * Real.cos (α + β)
  have hc : 0 < c := by exact_mod_cast hcr
  have hπ := Real.pi_pos
  have har : (0 : ℝ) < a := by rw [ha]; positivity
  have hbr : (0 : ℝ) < b := by rw [hb]; exact mul_pos (by nlinarith) hcr
  have haa : (a : ℝ) ^ 2 = c * (c - b) := by rw [ha, hb]; ring
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  -- `cos α = (b + c)/(2c)`
  have hcos : Real.cos α = ((b : ℝ) + c) / (2 * c) := by
    obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
    have hrelb : (b : ℝ) = c - (a : ℝ) ^ 2 / c := by rw [haa]; field_simp; ring
    obtain ⟨-, -, cα, -⟩ := tile_of_sides D₁ σ l0 l1 l2 hrelb
    rw [h0] at cα
    rw [eq_div_iff (by positivity)]
    have : (b : ℝ) * (2 * c * Real.cos α - (b + c)) = 0 := by linear_combination cα - haa
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hbr.ne'
    · linarith
  -- the base: `Λ c = L`, so the base is `L a / c`
  obtain ⟨o0, o1, -, hΛ⟩ := iso_scale D₁ hrel hT hshape
  have hbase : D₁.target.oppLen 1 = L * a / c := by
    rw [o1, show Lam D₁ = L / c by rw [← hleg0, o0]; field_simp]; ring
  -- subdivide by `c`
  obtain ⟨E, hEt, hEm⟩ := Erdos634.Realizable.cut_scale ⟨D₁, rfl, rfl⟩ c hc
  set Q0 := E.target.pts 0
  set Q1 := E.target.pts 1
  set Q2 := E.target.pts 2
  have e12 : dist Q1 Q2 = c * L := by
    show E.target.oppLen 0 = _; rw [hEt, oppLen_scaleN, hleg0]
  have e20 : dist Q2 Q0 = L * a := by
    show E.target.oppLen 1 = _; rw [hEt, oppLen_scaleN, hbase]; field_simp
  have e01 : dist Q0 Q1 = c * L := by
    show E.target.oppLen 2 = _; rw [hEt, oppLen_scaleN, hleg2]
  have h12 := sqd_of_dist _ _ _ e12
  have h20 := sqd_of_dist _ _ _ e20
  have h01 := sqd_of_dist _ _ _ e01
  -- the new vertex `A = Q1 + k (Q0 - Q1)`, `k = (c + b)/c`
  set k : ℝ := ((c : ℝ) + b) / c with hkdef
  have hk : k * c = c + b := by rw [hkdef]; field_simp
  obtain ⟨A, hA⟩ : ∃ A : Plane, A = Q1 + k • (Q0 - Q1) := ⟨_, rfl⟩
  have hA0 : A 0 = Q1 0 + k * (Q0 0 - Q1 0) := by rw [hA]; simp
  have hA1 : A 1 = Q1 1 + k * (Q0 1 - Q1 1) := by rw [hA]; simp
  have hcrE : cr Q0 Q1 Q2 ≠ 0 := cr_pts_ne_zero E.target
  have hk1 : k - 1 ≠ 0 := by
    intro h0
    have : k * c = c := by rw [show k = 1 by linarith, one_mul]
    linarith
  have hk0 : k ≠ 0 := by intro h0; rw [h0, zero_mul] at hk; linarith
  have c1 : cr Q2 A Q1 ≠ 0 := by
    have : cr Q2 A Q1 = k * cr Q0 Q1 Q2 := by unfold cr; rw [hA0, hA1]; ring
    rw [this]; exact mul_ne_zero hk0 hcrE
  have c2 : cr Q2 A Q0 ≠ 0 := by
    have : cr Q2 A Q0 = (k - 1) * cr Q0 Q1 Q2 := by unfold cr; rw [hA0, hA1]; ring
    rw [this]; exact mul_ne_zero hk1 hcrE
  have c3 : cr A Q2 Q1 ≠ 0 := by
    have : cr A Q2 Q1 = -(k * cr Q0 Q1 Q2) := by unfold cr; rw [hA0, hA1]; ring
    rw [this, neg_ne_zero]; exact mul_ne_zero hk0 hcrE
  -- distances
  have dAQ2 : dist A Q2 = c * L := dist_of_sqd _ _ _ (by positivity) (by
    rw [hA0, hA1]
    linear_combination (1 - k) * h12 + (k ^ 2 - k) * h01 + k * h20 + (k * L ^ 2) * haa
      + ((L : ℝ) ^ 2 * k * c) * hk)
  have dAQ0 : dist A Q0 = L * b := dist_of_sqd _ _ _ (by positivity) (by
    rw [hA0, hA1]
    linear_combination (k - 1) ^ 2 * h01 + ((L : ℝ) ^ 2 * ((k - 1) * c + b)) * hk)
  have dAQ1 : dist A Q1 = (c + b) * L := dist_of_sqd _ _ _ (by positivity) (by
    rw [hA0, hA1]
    linear_combination k ^ 2 * h01 + ((L : ℝ) ^ 2 * (k * c + c + b)) * hk)
  -- the pieces
  let Big : Erdos634.Geometry.Tri := triOf A Q2 Q1 c3
  let ABD : Erdos634.Geometry.Tri := triOf Q2 A Q0 c2
  -- the quadratic tiling of `ABD`
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  obtain ⟨F₀, hF₀t, hF₀m⟩ := Erdos634.Realizable.cut_scale (T := D₁.model) (t := D₁.model) (N := 1)
    ⟨Erdos634.Draft.CVCCevianCut.selfDissection D₁.model, rfl, rfl⟩ L hL
  have hcongF : F₀.target.Congruent ABD := by
    rw [hF₀t]
    refine congruent_of_oppLen ((Equiv.swap 0 1).trans σ) (fun j => ?_)
    rw [oppLen_scaleN]
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl
    · rw [show ((Equiv.swap 0 1).trans σ) 0 = σ 1 by simp, l1]
      show _ = dist A Q0; rw [dAQ0]
    · rw [show ((Equiv.swap 0 1).trans σ) 1 = σ 0 by simp, l0]
      show _ = dist Q0 Q2; rw [dist_comm, e20]
    · rw [show ((Equiv.swap 0 1).trans σ) 2 = σ 2 by
        simp only [Equiv.trans_apply]; rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)], l2]
      show _ = dist Q2 A; rw [dist_comm, dAQ2]; ring
  obtain ⟨F, hFc, hFm⟩ := Erdos634.Draft.CVCCevianCut.transport F₀ ABD hcongF
  -- the fan
  set tt : ℝ := (b : ℝ) / (c + b)
  have hP : Q0 = A + tt • (Q1 - A) := by
    have h' : k - tt * k = 1 := by
      rw [hkdef]; simp only [tt]; field_simp; ring
    calc Q0 = Q1 + (k - tt * k) • (Q0 - Q1) := by rw [h', one_smul]; abel
      _ = A + tt • (Q1 - A) := by rw [hA]; module
  have htt0 : 0 < tt := by positivity
  have htt1 : tt < 1 := by simp only [tt]; rw [div_lt_one (by positivity)]; linarith
  have cov := fan_cover Q2 A Q1 Q0 tt htt0 htt1 hP
  have dis := fan_disjoint Q2 A Q1 Q0 tt htt0 htt1 hP (by
    have : cr Q2 A Q1 = cr Q2 A Q1 := rfl; exact c1)
  have hEc : E.target.carrier = convexHull ℝ {Q2, Q0, Q1} := by
    rw [carrier_eq_hull]
    congr 1
    show ({Q0, Q1, Q2} : Set Plane) = {Q2, Q0, Q1}
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hFc' : F.target.carrier = convexHull ℝ {Q2, A, Q0} := by rw [hFc, carrier_triOf]
  have hBig : Big.carrier = convexHull ℝ {Q2, A, Q1} := by
    rw [carrier_triOf, Set.insert_comm A Q2]
  have hmodel : F.model = E.model := by rw [hFm, hF₀m, hEm]
  let D := unionCongruentDissection Big F E hmodel (by rw [hFc', hEc, hBig]; exact cov.symm)
    (by rw [hFc', hEc]; exact dis)
  have hDm : D.model = D₁.model := by
    show F.model = _; rw [hFm, hF₀m]
  refine ⟨D, ?_, ?_, ?_⟩
  · unfold TileSides; rw [hDm]; exact ⟨σ, h0, h1, h2, l0, l1, l2⟩
  · show Big.angleAt 0 = α
    refine angleAt_eq_of_cos Big 0 hα.le (by linarith) ?_
    show dist Q2 Q1 ^ 2 = dist Q1 A ^ 2 + dist A Q2 ^ 2 - 2 * dist Q1 A * dist A Q2 * Real.cos α
    rw [dist_comm Q2 Q1, dist_comm Q1 A, e12, dAQ1, dAQ2, hcos]; field_simp; ring
  · show Big.angleAt 2 = α
    refine angleAt_eq_of_cos Big 2 hα.le (by linarith) ?_
    show dist A Q2 ^ 2 = dist Q2 Q1 ^ 2 + dist Q1 A ^ 2 - 2 * dist Q2 Q1 * dist Q1 A * Real.cos α
    rw [dist_comm Q2 Q1, dist_comm Q1 A, e12, dAQ1, dAQ2, hcos]; field_simp; ring

/-- **Corollary `corollary:isoscelesalphaall`.** Let the tile have angles `(α, β, γ)` with
`3α + 2β = π` and `s` rational, and let `(a, b, c)` be the integer multiple of the tile with no
common factor. Then for some `N`, some isosceles triangle with base angles `α` can be `N`-tiled by
the tile. Specifically, if some isosceles triangle with base angles `α + β` and legs of length `L`
can be `N₁`-tiled, then `N = L² + c²N₁` tiles suffice.

"`(a, b, c)` is the integer multiple of the tile" is `a/c = s = 2 sin(α/2)` and `a² + cb = c²`
(`3α + 2β = π`, `lemma:anglesOK`); `s` rational follows. The triangle with base angles `α + β` has
its apex (angle `α`) at `B`; the new triangle has its base angles at `A` and `C`. -/
theorem isoscelesalphaall {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hα : 0 < α) (hβ : 0 < β)
    (a b c : ℕ) (ha : 0 < a) (h : a * a + c * b = c * c) (hprim : Nat.gcd (Nat.gcd a b) c = 1)
    (hs : (a : ℝ) / c = 2 * Real.sin (α / 2)) :
    (∃ (N : ℕ) (D : CongruentDissection N), TileSides D α β (2 * α + β) a b c ∧
      D.target.angleAt 0 = α ∧ D.target.angleAt 2 = α) ∧
    ∀ (N₁ : ℕ) (D₁ : CongruentDissection N₁) (L : ℕ), 0 < L →
      TileSides D₁ α β (2 * α + β) a b c →
      (D₁.target.angleAt 0 = α + β ∧ D₁.target.angleAt 1 = α ∧ D₁.target.angleAt 2 = α + β) →
      D₁.target.oppLen 0 = L → D₁.target.oppLen 2 = L →
      ∃ (N : ℕ) (D : CongruentDissection N), N = L ^ 2 + c ^ 2 * N₁ ∧
        TileSides D α β (2 * α + β) a b c ∧ D.target.angleAt 0 = α ∧ D.target.angleAt 2 = α := by
  have part2 : ∀ (N₁ : ℕ) (D₁ : CongruentDissection N₁) (L : ℕ), 0 < L →
      TileSides D₁ α β (2 * α + β) a b c →
      (D₁.target.angleAt 0 = α + β ∧ D₁.target.angleAt 1 = α ∧ D₁.target.angleAt 2 = α + β) →
      D₁.target.oppLen 0 = L → D₁.target.oppLen 2 = L →
      ∃ (N : ℕ) (D : CongruentDissection N), N = L ^ 2 + c ^ 2 * N₁ ∧
        TileSides D α β (2 * α + β) a b c ∧ D.target.angleAt 0 = α ∧ D.target.angleAt 2 = α := by
    intro N₁ D₁ L hL hT hsh h0 h2
    obtain ⟨D, hD, A0, A2⟩ := iso_alpha_glue D₁ hrel hT hsh hL h0 h2
    exact ⟨_, D, by ring, hD, A0, A2⟩
  refine ⟨?_, part2⟩
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at h; omega
    · exact h0
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hq : ∃ q : ℚ, 2 * Real.sin (α / 2) = q := ⟨(a : ℚ) / c, by rw [← hs]; push_cast; rfl⟩
  obtain ⟨N₀, D₀, a', b', c', hT₀, A0, A1, A2⟩ := isoscelesall hrel hα hβ hq
  obtain ⟨-, -, -, -, hc', ha', hb', -⟩ := model_facts D₀ hrel hT₀
  have ht : 2 * Real.cos (α + β) = (a : ℝ) / c := by
    rw [hs, show α + β = Real.pi / 2 - α / 2 by linarith, Real.cos_pi_div_two_sub]
  have hbr : (b : ℝ) = (1 - ((a : ℝ) / c) ^ 2) * c := by
    have : (c : ℝ) * b = c * c - a * a := by
      have := congrArg (fun n : ℕ => (n : ℝ)) h; push_cast at this; linarith
    field_simp; linarith
  set r := c' / c
  have hr : 0 < r := div_pos hc' hcr
  have e1 : a' = r * a := by rw [ha', ht]; simp only [r]; field_simp
  have e2 : b' = r * b := by rw [hb', ht, hbr]; simp only [r]; field_simp
  have e3 : c' = r * c := by simp only [r]; field_simp
  rw [e1, e2, e3] at hT₀
  obtain ⟨D₁, hT₁, hA⟩ := unscale hr hT₀
  have hsh : D₁.target.angleAt 0 = α + β ∧ D₁.target.angleAt 1 = α ∧ D₁.target.angleAt 2 = α + β :=
    ⟨by rw [hA, A0], by rw [hA, A1], by rw [hA, A2]⟩
  obtain ⟨L, hL, h0, h2⟩ := iso_leg_nat D₁ hrel hT₁ hsh hprim
  obtain ⟨N, D, -, hD, B0, B2⟩ := part2 _ D₁ L hL hT₁ hsh h0 h2
  exact ⟨N, D, hD, B0, B2⟩

end TriangleTiling.ThreeAlpha
