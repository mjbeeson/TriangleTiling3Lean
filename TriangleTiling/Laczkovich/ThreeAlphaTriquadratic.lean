/-
The `a`-relation (Section 4, "There is an `a`-relation") and the triquadratic case of Section 6
("Rationality of the tile") of M. Beeson, *Triangle tiling: the case 3α + 2β = π*
(arXiv 1206.2229v4), and `theorem:rationaltile`.

`Γ_a` and "witnesses no `a`-relation" as in `TriangleTiling.ThreeAlpha.Relations`. Theorems 7, 8
and Corollary 1 use the setting of `theorem:M1M2`: `A, B, C` counterclockwise with the angles
listed at `A, B, C`, and `M₁`, `M₂` from `Φ₁`, `Φ₂` (`M₁` is the `M` of Theorem 1, by
`remark:Phi1iscoloring`).
-/
import TriangleTiling.Laczkovich.ThreeAlphaRational
import TriangleTiling.ThreeAlpha.Relations
import TriangleTiling.ThreeAlpha.ARelation

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open Erdos634.BeesonColoring

variable {N : ℕ} (D : CongruentDissection N)


/-! ### Relabelling and mirroring the target -/

section Normalize

open Erdos634.MirrorGauge in
theorem mirror_angleAt (T : Tri) (k : Fin 3) : (Erdos634.MirrorGauge.Tri.mirror T).angleAt k = T.angleAt k := by
  have hn : ∀ v : Plane, ‖mirrorL v‖ = ‖v‖ := by
    intro v
    have := mirrorPt_dist v 0
    have h0 : mirrorPt 0 = 0 := by ext i; fin_cases i <;> simp
    rw [h0, dist_zero_right, dist_zero_right] at this
    exact this
  let f : Plane →ₗᵢ[ℝ] Plane := ⟨mirrorL, hn⟩
  unfold Tri.angleAt cornerAngle
  exact f.toAffineIsometry.angle_map _ _ _

open Erdos634.MirrorGauge in
theorem mirror_oppLen (T : Tri) (k : Fin 3) : (Erdos634.MirrorGauge.Tri.mirror T).oppLen k = T.oppLen k :=
  mirrorPt_dist _ _

theorem relabel_angleAt (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (relabelTarget D σ).target.angleAt k = D.target.angleAt (σ k) := by
  have d1 : σ k ≠ σ (k + 1) := σ.injective.ne (fin3_ne_add_one k)
  have d2 : σ k ≠ σ (k + 2) := σ.injective.ne ((by decide : ∀ x : Fin 3, x ≠ x + 2) k)
  have d12 : σ (k + 1) ≠ σ (k + 2) := σ.injective.ne ((by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) k)
  show cornerAngle (D.target.pts (σ (k + 1))) (D.target.pts (σ k)) (D.target.pts (σ (k + 2))) = _
  unfold Tri.angleAt cornerAngle
  rcases others _ _ _ d1 d2 d12 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
  exact EuclideanGeometry.angle_comm _ _ _

theorem relabel_oppLen (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (relabelTarget D σ).target.oppLen k = D.target.oppLen (σ k) := by
  have d1 : σ k ≠ σ (k + 1) := σ.injective.ne (fin3_ne_add_one k)
  have d2 : σ k ≠ σ (k + 2) := σ.injective.ne ((by decide : ∀ x : Fin 3, x ≠ x + 2) k)
  have d12 : σ (k + 1) ≠ σ (k + 2) := σ.injective.ne ((by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) k)
  show dist (D.target.pts (σ (k + 1))) (D.target.pts (σ (k + 2))) = _
  unfold Tri.oppLen
  rcases others _ _ _ d1 d2 d12 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
  exact dist_comm _ _

theorem similar_of_relabel (σ : Equiv.Perm (Fin 3)) (h : SimilarTM (relabelTarget D σ)) :
    SimilarTM D := by
  obtain ⟨μ, τ, hτ⟩ := h
  refine ⟨μ, σ.symm.trans τ, fun k => ?_⟩
  obtain ⟨k', rfl⟩ := σ.surjective k
  have := hτ k'
  rw [relabel_angleAt, relabel_oppLen] at this
  simpa using this

theorem similar_of_mirror (h : SimilarTM (Erdos634.MirrorGauge.CongruentDissection.mirror D)) :
    SimilarTM D := by
  obtain ⟨μ, τ, hτ⟩ := h
  refine ⟨μ, τ, fun k => ?_⟩
  have := hτ k
  change (Erdos634.MirrorGauge.Tri.mirror D.target).angleAt k = _ ∧
    (Erdos634.MirrorGauge.Tri.mirror D.target).oppLen k = _ at this
  rw [mirror_angleAt, mirror_oppLen] at this
  exact this

/-- **Normalizing the labels**: for a listed order of the angles of `ABC`, there is a tiling with the
same tile and tile count, not similar to the tile if the original is not, with `A, B, C`
counterclockwise and the angles in that order. -/
theorem normalize {x y z : ℝ} (hxyz : TgtAngles D x y z) (hns : ¬ SimilarTM D) :
    ∃ D' : CongruentDissection N, D'.model = D.model ∧ ¬ SimilarTM D' ∧ 0 < D'.target.det ∧
      D'.target.angleAt 0 = x ∧ D'.target.angleAt 1 = y ∧ D'.target.angleAt 2 = z := by
  obtain ⟨σ, h0, h1, h2⟩ := hxyz
  set D₁ := relabelTarget D σ
  have hns₁ : ¬ SimilarTM D₁ := fun h => hns (similar_of_relabel D σ h)
  have a0 : D₁.target.angleAt 0 = x := by rw [relabel_angleAt]; exact h0
  have a1 : D₁.target.angleAt 1 = y := by rw [relabel_angleAt]; exact h1
  have a2 : D₁.target.angleAt 2 = z := by rw [relabel_angleAt]; exact h2
  rcases D₁.target.det_pos_or_neg with hd | hd
  · exact ⟨D₁, rfl, hns₁, hd, a0, a1, a2⟩
  · set D₂ := Erdos634.MirrorGauge.CongruentDissection.mirror D₁
    refine ⟨D₂, rfl, fun h => hns₁ (similar_of_mirror D₁ h), ?_, ?_, ?_, ?_⟩
    · change 0 < (Erdos634.MirrorGauge.Tri.mirror D₁.target).det
      rw [Erdos634.MirrorGauge.Tri.det_mirror]; linarith
    · change (Erdos634.MirrorGauge.Tri.mirror D₁.target).angleAt 0 = x
      rw [mirror_angleAt]; exact a0
    · change (Erdos634.MirrorGauge.Tri.mirror D₁.target).angleAt 1 = y
      rw [mirror_angleAt]; exact a1
    · change (Erdos634.MirrorGauge.Tri.mirror D₁.target).angleAt 2 = z
      rw [mirror_angleAt]; exact a2

theorem tileSides_of_model {D' : CongruentDissection N} (hm : D'.model = D.model)
    {α β γ a b c : ℝ} (hT : TileSides D α β γ a b c) : TileSides D' α β γ a b c := by
  unfold TileSides; rw [hm]; exact hT

end Normalize


/-- A rational tile has an `a`-relation: `den · a = num · c`. -/
theorem arel_of_rational {a b c : ℝ} (ha : 0 < a) (hc : 0 < c) (hr : RationalTile a b c) :
    ARelation a b c := by
  obtain ⟨⟨q, hq⟩, -, -⟩ := hr
  have hq0 : 0 < q := by
    have : (0 : ℝ) < q := by rw [← hq]; positivity
    exact_mod_cast this
  have hnum : 0 < q.num := Rat.num_pos.mpr hq0
  refine ⟨q.den, 0, q.num.toNat, q.den_pos, ?_⟩
  have e1 : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
    have := Int.toNat_of_nonneg hnum.le
    exact_mod_cast this
  have e2 : (q : ℝ) = q.num / q.den := by
    rw [← Rat.cast_def]
  rw [e1, Nat.cast_zero, zero_mul, zero_add]
  rw [div_eq_iff hc.ne', e2] at hq
  have hd : (q.den : ℝ) ≠ 0 := by positivity
  field_simp at hq
  linarith

/-- An integer that is the square of a rational is the square of an integer. -/
theorem int_sq_of_rat_sq {m : ℤ} {k : ℚ} (h : k ^ 2 = m) : ∃ j : ℤ, m = j ^ 2 := by
  have hd : k.den ^ 2 = 1 := by
    have := congrArg Rat.den h
    rw [Rat.den_pow, Rat.den_intCast] at this
    exact this
  have hd1 : k.den = 1 := by
    have := (Nat.pow_eq_one.mp hd).resolve_right (by norm_num)
    exact this
  refine ⟨k.num, ?_⟩
  have hk : k = k.num := by
    rw [← Rat.num_div_den k, hd1]; simp
  have : ((m : ℚ)) = (k.num : ℚ) ^ 2 := by rw [← h, ← hk]
  exact_mod_cast this

open Classical in
/-- **Lemma `lemma:apropagation`** (propagation in `Γ_a`). Let `ABC` be `N`-tiled by a tile with
sides `(a, b, c)` and angles `(α, β, γ)`, `3α + 2β = π`, not similar to `ABC`, and suppose the
tiling witnesses no `a`-relation. Then `Γ_a` propagates links (if `PQ` is a link there is a link
`QR`); the in-degree and out-degree of every node are `1`; and no link starts on the boundary of
`ABC`. -/
theorem apropagation {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hnorel : ¬ HasRelation D.toDissection (edgeType D α)) :
    (∀ P Q, IsLink D.toDissection (edgeType D α) P Q →
      ∃ R, IsLink D.toDissection (edgeType D α) Q R) ∧
    (∀ v : Plane, (∃ w, IsLink D.toDissection (edgeType D α) v w ∨
        IsLink D.toDissection (edgeType D α) w v) →
      ((vertexFinset D.toDissection).filter
          fun u => IsLink D.toDissection (edgeType D α) u v).card = 1 ∧
      ((vertexFinset D.toDissection).filter
          fun w => IsLink D.toDissection (edgeType D α) v w).card = 1) ∧
    (∀ X Y, IsLink D.toDissection (edgeType D α) X Y → X ∉ frontier D.target.carrier) := by
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  exact propagation_irr D (angles D hrel hT' hns).1 hrel (threeAlphaData_of_sides D hrel hT) hnorel


/-- Theorems 5 and 6 for any labelling: if the angles of `ABC` are, in some order, one of the four
non-triquadratic shapes, the tile is rational. -/
theorem rational_listed {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) {x y z : ℝ} (hxyz : TgtAngles D x y z)
    (hcase : (x = β ∧ y = 3 * α ∧ z = β) ∨ (x = α + β ∧ y = α ∧ z = α + β) ∨
      (x = α ∧ y = α + 2 * β ∧ z = α) ∨ (x = 2 * α ∧ y = α ∧ z = 2 * β)) :
    RationalTile a b c := by
  obtain ⟨D', hm, hns', hccw, e0, e1, e2⟩ := normalize D hxyz hns
  have hT' := tileSides_of_model D hm hT
  obtain ⟨n, ε, -, M₁, M₂, -, -, -, -, -, -, h₁, h₂⟩ := Mdef D' hrel hT' hns'
  have r5 := rationaliso D' hrel hT' hns' hccw h₁ h₂
  have r6 := shape45 D' hrel hT' hns' hccw h₁ h₂
  dsimp only at r5 r6
  rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact (r5.1 ⟨e0, e1, e2⟩).1
  · exact (r5.2 ⟨e0, e1, e2⟩).1
  · exact (r6.2.2 (Or.inl ⟨e0, e1, e2⟩)).2.2
  · exact (r6.2.2 (Or.inr ⟨e0, e1, e2⟩)).2.2

/-- **Theorem `theorem:arelation`.** Let `ABC` be `N`-tiled by a tile with sides `(a, b, c)` and
angles `(α, β, γ)`, `3α + 2β = π`, not similar to `ABC`. Then there is an `a`-relation
`j a = p b + q c`, with `p, q, j` nonnegative integers and `j > 0`. -/
theorem arelation {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) : ARelation a b c := by
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  have hirr := (angles D hrel hT' hns).1
  have h := threeAlphaData_of_sides D hrel hT
  have hns3 := not_triple3 D hrel hT' hns
  obtain ⟨ha, -, hc, -, -⟩ := model_abc_pos h
  obtain ⟨h5, -, -⟩ := shapes D hrel hT' hns
  have beta : (∃ k, D.target.angleAt k = β) → ARelation a b c := fun hk =>
    arel_of_edges D hirr hrel h (lone_beta_hasRelation D hirr hrel h hns3 hk)
  rcases h5 with s1 | s2 | s3 | s4 | s5
  · exact arel_of_rational ha hc
      (rational_listed D hrel hT hns s1 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
  · obtain ⟨σ, e, -, -⟩ := s2; exact beta ⟨_, e⟩
  · exact arel_of_rational ha hc
      (rational_listed D hrel hT hns s3 (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  · obtain ⟨σ, -, e, -⟩ := s4; exact beta ⟨_, e⟩
  · exact arel_of_rational ha hc
      (rational_listed D hrel hT hns s5 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))

/-- **Theorem `theorem:tqsquare`.** If a triquadratic triangle (angles `(2α, β, α + β)`) is tiled
by `N` copies of `T`, then `s² = 2M²/(N + M²)`. In particular `s²` and `b/c = 1 - s²` are rational,
so `rank L ≥ 1` (`lemma:relationlattice`), and `N > M²`. Here `M = M₁ = M₂` (`lemma:kappa`). -/
theorem tqsquare {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) (hccw : 0 < D.target.det)
    {M₁ M₂ : ℤ} (h₁ : PhiR (Phi1 (α + β) (baseDir D)) D.target = M₁ * (a + b + c))
    (h₂ : PhiR (Phi2 (α + β) (baseDir D)) D.target = M₂ * (a - b - c))
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧
      D.target.angleAt 2 = α + β) :
    (a / c) ^ 2 = 2 * M₁ ^ 2 / (N + M₁ ^ 2) ∧ (∃ q : ℚ, (a / c) ^ 2 = q) ∧
      (∃ q : ℚ, b / c = q) ∧ 1 ≤ Module.finrank ℤ (relLattice a b c) ∧ M₁ ^ 2 < (N : ℤ) := by
  have m := M1M2 D hrel hT hns hccw h₁ h₂
  dsimp only at m
  obtain ⟨e1, e2⟩ := m.1 hshape
  have ar := shapeareas D hrel hT
  dsimp only at ar
  have a1 := ar.1 hshape
  obtain ⟨-, -, -, hS, hc, ha, hb, ht0, ht1, -, -⟩ := model_facts D hrel hT
  have hst : a / c = 2 * Real.cos (α + β) := by rw [ha]; field_simp
  rw [hst] at e1 e2 a1
  set t := 2 * Real.cos (α + β)
  have hΛ : 0 < Lam D := div_pos (circumdiam_pos _) (circumdiam_pos _)
  have eN : (N : ℝ) = Lam D ^ 2 * (2 - t ^ 2) := by rw [← a1]; field_simp
  have hden : (N : ℝ) + (M₁ : ℝ) ^ 2 = 2 * Lam D ^ 2 := by rw [eN, e1]; ring
  have hden0 : (N : ℝ) + (M₁ : ℝ) ^ 2 ≠ 0 := by rw [hden]; positivity
  have hsq : t ^ 2 = 2 * (M₁ : ℝ) ^ 2 / (N + M₁ ^ 2) := by
    rw [eq_div_iff hden0, hden, e1]; ring
  have hbc : b / c = 1 - t ^ 2 := by rw [hb]; field_simp
  set q : ℚ := 1 - 2 * M₁ ^ 2 / (N + M₁ ^ 2)
  have hq : b / c = q := by rw [hbc, hsq]; simp only [q]; push_cast; ring
  refine ⟨by rw [hst]; exact hsq, ⟨2 * M₁ ^ 2 / (N + M₁ ^ 2), by rw [hst, hsq]; push_cast; ring⟩,
    ⟨q, hq⟩, ?_, ?_⟩
  · -- A nonzero vector `(0, den q, -num q)` of `L`.
    have hv : (![0, (q.den : ℤ), -q.num] : Fin 3 → ℤ) ∈ relLattice a b c := by
      show ((0 : ℤ) : ℝ) * a + ((q.den : ℤ) : ℝ) * b + ((-q.num : ℤ) : ℝ) * c = 0
      have hqd : (q : ℝ) = q.num / q.den := by rw [← Rat.cast_def]
      have hd : (q.den : ℝ) ≠ 0 := by positivity
      rw [div_eq_iff hc.ne', hqd] at hq
      field_simp at hq
      push_cast
      linarith
    have : 0 < Module.finrank ℤ (relLattice a b c) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨_, hv⟩, fun h0 => by
        have := congrArg (fun v : relLattice a b c => (v : Fin 3 → ℤ) 1) h0
        simp at this⟩
    omega
  · have : (M₁ : ℝ) ^ 2 < N := by
      rw [eN, e1]
      have : 0 < 1 - t ^ 2 := by nlinarith
      nlinarith [mul_pos (pow_pos hΛ 2) this]
    exact_mod_cast this

/-- **Theorem `theorem:tqrational`.** Suppose a triquadratic triangle is tiled by `N` copies of
`T`. Then `T` is rational, and `2(N + M²)` is a perfect square. -/
theorem tqrational {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) (hccw : 0 < D.target.det)
    {M₁ M₂ : ℤ} (h₁ : PhiR (Phi1 (α + β) (baseDir D)) D.target = M₁ * (a + b + c))
    (h₂ : PhiR (Phi2 (α + β) (baseDir D)) D.target = M₂ * (a - b - c))
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧
      D.target.angleAt 2 = α + β) :
    RationalTile a b c ∧ ∃ k : ℤ, 2 * ((N : ℤ) + M₁ ^ 2) = k ^ 2 := by
  obtain ⟨hs2, ⟨q₂, hq₂⟩, -, -, -⟩ := tqsquare D hrel hT hns hccw h₁ h₂ hshape
  obtain ⟨j, p, q, hj, hjr⟩ := arelation D hrel hT hns
  obtain ⟨-, -, -, -, hc, ha, hb, ht0, ht1, -, -⟩ := model_facts D hrel hT
  have hst : a / c = 2 * Real.cos (α + β) := by rw [ha]; field_simp
  rw [hst] at hs2 hq₂
  set t := 2 * Real.cos (α + β)
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have ht : t = ((p * (1 - q₂) + q) / j : ℚ) := by
    push_cast
    rw [eq_div_iff hj0, ← hq₂]
    rw [ha, hb] at hjr
    have := mul_right_cancel₀ hc.ne' (show (j * t) * c = (p * (1 - t ^ 2) + q) * c by linarith)
    linarith
  refine ⟨rationalTile_of hc ha hb ht0 ht1 ht, ?_⟩
  set tq : ℚ := (p * (1 - q₂) + q) / j
  have htq0 : (tq : ℝ) ≠ 0 := by rw [← ht]; exact ht0.ne'
  have hden0 : (N : ℝ) + (M₁ : ℝ) ^ 2 ≠ 0 := by
    intro h0; rw [h0, div_zero] at hs2; nlinarith
  have hK : (((2 * M₁ / tq) ^ 2 : ℚ) : ℝ) = ((2 * ((N : ℤ) + M₁ ^ 2) : ℤ) : ℝ) := by
    push_cast
    rw [← ht, div_pow, div_eq_iff (by positivity), hs2]
    field_simp
  have hK' : (2 * M₁ / tq) ^ 2 = ((2 * ((N : ℤ) + M₁ ^ 2) : ℤ) : ℚ) := by exact_mod_cast hK
  obtain ⟨k, hk⟩ := int_sq_of_rat_sq hK'
  exact ⟨k, hk⟩

-- `m < k` is part of the printed hypotheses; the proof does not need it.
set_option linter.unusedVariables false in
/-- **Corollary `corollary:tqparameters`.** If a triquadratic triangle is tiled by `N` copies of
the tile, written `(a, b, c) = τ (mk, k² - m², k²)` as in `lemma:gsquare` with `gcd (m, k) = 1`
and `m < k`, then `m ∣ M`, and with `j = M/m`: `N = j²(2k² - m²)`, `M = jm`, `Λ = jk`,
`|BC| = jm(2k² - m²)τ`, `|CA| = jk(k² - m²)τ`, `|AB| = jk³τ`. -/
theorem tqparameters {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) (hccw : 0 < D.target.det)
    {M₁ M₂ : ℤ} (h₁ : PhiR (Phi1 (α + β) (baseDir D)) D.target = M₁ * (a + b + c))
    (h₂ : PhiR (Phi2 (α + β) (baseDir D)) D.target = M₂ * (a - b - c))
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧
      D.target.angleAt 2 = α + β)
    {τ : ℝ} {m k : ℕ} (hτ : 0 < τ) (hmk : Nat.Coprime m k) (hlt : m < k)
    (ha : a = τ * (m * k)) (hb : b = τ * (k ^ 2 - m ^ 2)) (hc : c = τ * k ^ 2) :
    (m : ℤ) ∣ M₁ ∧
      let j := M₁ / m
      (N : ℤ) = j ^ 2 * (2 * k ^ 2 - m ^ 2) ∧ M₁ = j * m ∧ Lam D = j * k ∧
      D.target.oppLen 0 = j * m * (2 * k ^ 2 - m ^ 2) * τ ∧
      D.target.oppLen 1 = j * k * (k ^ 2 - m ^ 2) * τ ∧ D.target.oppLen 2 = j * k ^ 3 * τ := by
  have h := threeAlphaData_of_sides D hrel hT
  obtain ⟨hα, hβ, -, hS, hc0, hat, hbt, ht0, ht1, -, -⟩ := model_facts D hrel hT
  set t := 2 * Real.cos (α + β)
  have hk0 : (0 : ℝ) < k := by
    have : (0 : ℝ) < τ * k ^ 2 := by rw [← hc]; exact hc0
    have hk : (k : ℝ) ≠ 0 := fun e => by rw [e] at this; simp at this
    positivity
  have hm0 : (0 : ℝ) < m := by
    have ha0 := (model_abc_pos h).1
    rw [ha] at ha0
    by_contra hm; push Not at hm
    have : (m : ℝ) = 0 := le_antisymm hm (Nat.cast_nonneg m)
    rw [this] at ha0; simp at ha0
  have htmk : t = m / k := by
    have e : a = t * c := hat
    rw [ha, hc] at e
    field_simp at e ⊢
    nlinarith [mul_pos hτ hk0]
  have hst : a / c = t := by rw [hat]; field_simp
  have m1 := (M1M2 D hrel hT hns hccw h₁ h₂).1
  dsimp only at m1
  obtain ⟨eM, -⟩ := m1 hshape
  rw [hst] at eM
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨-, r2, -, -, r5, -, -, -⟩ := r
  rw [div_eq_iff hS.ne'] at r2 r5
  have s0 := target_side D hrel hT 0
  have s1 := target_side D hrel hT 1
  have s2 := target_side D hrel hT 2
  rw [hshape.1, r5] at s0
  rw [hshape.2.1, r2] at s1
  rw [hshape.2.2] at s2
  have e0 : D.target.oppLen 0 = Lam D * c * (t * (2 - t ^ 2)) := by
    rw [s0]; field_simp; ring
  have e1 : D.target.oppLen 1 = Lam D * c * (1 - t ^ 2) := by
    rw [s1]; field_simp; ring
  have e2 : D.target.oppLen 2 = Lam D * c := by rw [s2]; field_simp
  -- `|AB|` is a sum of tile edges.
  have habc : ∀ (i : Fin N) (l : Fin 3), dist ((D.tile i).pts l) ((D.tile i).pts (l + 1)) = a ∨
      dist ((D.tile i).pts l) ((D.tile i).pts (l + 1)) = b ∨
      dist ((D.tile i).pts l) ((D.tile i).pts (l + 1)) = c := by
    intro i l
    obtain ⟨ρ, -, l0, -, l1, -, l2⟩ := tile_threeAlpha D h i
    have : dist ((D.tile i).pts l) ((D.tile i).pts (l + 1)) = (D.tile i).oppLen (l + 2) := by
      unfold Tri.oppLen
      rw [show l + 2 + 1 = l by fin_cases l <;> rfl, show l + 2 + 2 = l + 1 by fin_cases l <;> rfl]
    rw [this]
    obtain ⟨u, hu⟩ := ρ.surjective (l + 2)
    rw [← hu]
    fin_cases u
    · exact Or.inl l0
    · exact Or.inr (Or.inl l1)
    · exact Or.inr (Or.inr l2)
  obtain ⟨P, Q, R, hPQR, -⟩ := D.toDissection.side_walk_abc 0 a b c habc
  have hAB : dist (D.target.pts 0) (D.target.pts (0 + 1)) = D.target.oppLen 2 := rfl
  rw [hAB, e2, ha, hb, hc] at hPQR
  set Λ := Lam D with hΛdef
  -- `Λ k² = P m k + Q (k² - m²) + R k²`, and `Λ = M₁ k / m`.
  have hZ : Λ * k ^ 2 = ((P * (m * k) + Q * (k ^ 2 - m ^ 2) + R * k ^ 2 : ℤ) : ℝ) := by
    push_cast
    have := mul_left_cancel₀ hτ.ne' (show τ * (Λ * k ^ 2) = τ * (P * (m * k) + Q * (k ^ 2 - m ^ 2)
      + R * k ^ 2) by linarith)
    linarith
  have hΛ : Λ = M₁ * k / m := by rw [eq_div_iff hm0.ne', eM, htmk]; field_simp
  have hdiv : (m : ℤ) ∣ M₁ * k ^ 3 := by
    refine ⟨P * (m * k) + Q * (k ^ 2 - m ^ 2) + R * k ^ 2, ?_⟩
    have : ((M₁ * k ^ 3 : ℤ) : ℝ) = ((m * (P * (m * k) + Q * (k ^ 2 - m ^ 2) + R * k ^ 2) : ℤ) : ℝ) := by
      have hZ' := hZ
      push_cast at hZ' ⊢
      rw [← hZ', hΛ]; field_simp
    exact_mod_cast this
  have hcop : IsCoprime (m : ℤ) ((k : ℤ) ^ 3) :=
    (Nat.isCoprime_iff_coprime.mpr hmk).pow_right
  have hmM : (m : ℤ) ∣ M₁ := hcop.dvd_of_dvd_mul_right hdiv
  refine ⟨hmM, ?_⟩
  intro j
  have hj : M₁ = j * m := (Int.ediv_mul_cancel hmM).symm
  have hjR : (M₁ : ℝ) = j * m := by exact_mod_cast hj
  have hΛj : Λ = j * k := by rw [hΛ, hjR]; field_simp
  have ar := (shapeareas D hrel hT).1 hshape
  rw [hst, ← hΛdef] at ar
  have hΛ0 : Λ ≠ 0 := (div_pos (circumdiam_pos _) (circumdiam_pos _)).ne'
  have eN : (N : ℝ) = Λ ^ 2 * (2 - t ^ 2) := by rw [← ar]; field_simp
  refine ⟨?_, hj, hΛj, ?_, ?_, ?_⟩
  · have : (N : ℝ) = ((j ^ 2 * (2 * k ^ 2 - m ^ 2) : ℤ) : ℝ) := by
      rw [eN, hΛj, htmk]; push_cast; field_simp
    exact_mod_cast this
  · rw [e0, hΛj, htmk, hc]; field_simp
  · rw [e1, hΛj, htmk, hc]; field_simp
  · rw [e2, hΛj, hc]; ring

/-- **Theorem `theorem:rationaltile`.** Let `ABC` be a triangle, not similar to `T`, tiled by
copies of a triangle `T` with `3α + 2β = π`. Then `T` is rational. -/
theorem rationaltile {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) : RationalTile a b c := by
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  obtain ⟨h5, -, -⟩ := shapes D hrel hT' hns
  rcases h5 with s1 | s2 | s3 | s4 | s5
  · exact rational_listed D hrel hT hns s1 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  · exact rational_listed D hrel hT hns s2 (Or.inl ⟨rfl, rfl, rfl⟩)
  · exact rational_listed D hrel hT hns s3 (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  · obtain ⟨D', hm, hns', hccw, e0, e1, e2⟩ := normalize D s4 hns
    have hT₂ := tileSides_of_model D hm hT
    obtain ⟨n, ε, -, M₁, M₂, -, -, -, -, -, -, h₁, h₂⟩ := Mdef D' hrel hT₂ hns'
    exact (tqrational D' hrel hT₂ hns' hccw h₁ h₂ ⟨e0, e1, e2⟩).1
  · exact rational_listed D hrel hT hns s5 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))

end TriangleTiling.ThreeAlpha
