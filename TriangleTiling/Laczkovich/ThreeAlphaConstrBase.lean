/-
Bridges from Bonfioli's construction theorems (Erdos634, UNAUDITED) to the vocabulary of
M. Beeson, *Triangle tiling: the case 3α + 2β = π* (arXiv 1206.2229v4): relabelling, the tile's
angles from its sides, and the target's angles from its sides.
-/
import TriangleTiling.ThreeAlpha.SidesAngles
import TriangleTiling.ThreeAlpha.Basic
import TriangleTiling.ThreeAlpha.Defs
import TriangleTiling.RightTile.AllC
import Erdos634.Draft.FDBBaseBetaE1
import Erdos634.DissectionMap
import TriangleTiling.Laczkovich.ThreeAlphaScaling
import TriangleTiling.ThreeAlpha.Areas

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry EuclideanGeometry

variable {N : ℕ}

theorem relabelTarget_target (D : CongruentDissection N) (ρ : Equiv.Perm (Fin 3)) :
    (relabelTarget D ρ).target = D.target.relabel ρ := rfl

/-- Bonfioli's `HasSides` is our labelling after a relabelling. -/
theorem hasSides_relabel {T : Tri} {a b c : ℝ} (h : Erdos634.Draft.FDBBaseBetaE1.HasSides T a b c) :
    ∃ τ : Equiv.Perm (Fin 3), (T.relabel τ).oppLen 0 = a ∧ (T.relabel τ).oppLen 1 = b ∧
      (T.relabel τ).oppLen 2 = c := by
  obtain ⟨τ, h1, h2, h3⟩ := h
  exact ⟨τ, h1, h2, h3⟩

/-- A tile with sides `(a, b, c)` opposite its vertices `τ 0, τ 1, τ 2`, `b = c - a²/c`: its
angles there are `(α, β, γ)` with `3α + 2β = π`, and `cos α`, `cos β` are given by the sides. -/
theorem tile_of_sides (D : CongruentDissection N) (τ : Equiv.Perm (Fin 3)) {a b c : ℝ}
    (ha : D.model.oppLen (τ 0) = a) (hb : D.model.oppLen (τ 1) = b) (hc : D.model.oppLen (τ 2) = c)
    (hrel : b = c - a ^ 2 / c) :
    let α := D.model.angleAt (τ 0)
    let β := D.model.angleAt (τ 1)
    TileSides D α β (D.model.angleAt (τ 2)) a b c ∧ 3 * α + 2 * β = Real.pi ∧
      a ^ 2 = b ^ 2 + c ^ 2 - 2 * b * c * Real.cos α ∧
      b ^ 2 = c ^ 2 + a ^ 2 - 2 * c * a * Real.cos β := by
  intro α β
  set T := D.model.relabel τ
  have l0 : T.oppLen 0 = a := by rw [oppLen_relabel]; exact ha
  have l1 : T.oppLen 1 = b := by rw [oppLen_relabel]; exact hb
  have l2 : T.oppLen 2 = c := by rw [oppLen_relabel]; exact hc
  have e0 : T.angleAt 0 = α := angleAt_relabel _ _ _
  have e1 : T.angleAt 1 = β := angleAt_relabel _ _ _
  refine ⟨⟨τ, rfl, rfl, rfl, ha, hb, hc⟩, ?_, ?_, ?_⟩
  · have hABC : AffineIndependent ℝ ![T.pts 0, T.pts 1, T.pts 2] := by
      convert T.indep using 1; ext k : 1; fin_cases k <;> rfl
    have key := (anglesOK hABC).mpr (by
      have h1 : dist (T.pts 2) (T.pts 0) = b := l1
      have h2 : dist (T.pts 0) (T.pts 1) = c := l2
      have h3 : dist (T.pts 1) (T.pts 2) = a := l0
      rw [h1, h2, h3, hrel])
    rw [← e0, ← e1]
    have q0 : T.angleAt 0 = ∠ (T.pts 1) (T.pts 0) (T.pts 2) := rfl
    have q1 : T.angleAt 1 = ∠ (T.pts 0) (T.pts 1) (T.pts 2) := by
      show ∠ (T.pts 2) (T.pts 1) (T.pts 0) = _
      exact EuclideanGeometry.angle_comm _ _ _
    rw [q0, q1]; exact key
  · have := cos_angleAt T 0
    rw [e0] at this
    simp only [Fin.isValue, zero_add] at this
    rw [l0, l1, l2] at this
    exact this
  · have := cos_angleAt T 1
    rw [e1] at this
    rw [l1, show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, l2, l0] at this
    exact this

/-- A congruent dissection moved by an isometry of the plane; the model tile is unchanged. -/
noncomputable def isoDissection (f : Plane ≃ᵢ Plane) (D : CongruentDissection N) :
    CongruentDissection N :=
  { Erdos634.DissectionMap.mapDissection f.toRealAffineIsometryEquiv.toAffineEquiv D.toDissection with
    model := D.model
    tiles_congruent := fun i => by
      obtain ⟨g, σ, hg⟩ := D.tiles_congruent i
      refine ⟨f.symm.trans g, σ, fun k => ?_⟩
      show g (f.symm (f ((D.tile i).pts k))) = _
      rw [f.symm_apply_apply, hg] }

theorem isoDissection_target_pts (f : Plane ≃ᵢ Plane) (D : CongruentDissection N) (k : Fin 3) :
    (isoDissection f D).target.pts k = f (D.target.pts k) := rfl

/-- **Transport.** If the target of `D`, scaled by `r > 0`, is congruent to `T₀`, then `T₀` itself
is `N`-tiled by the model of `D` scaled by `r`. -/
theorem transport (D : CongruentDissection N) (T₀ : Tri) {r : ℝ} (hr : 0 < r)
    (h : (scaleTri D.target r hr.ne').Congruent T₀) :
    ∃ D' : CongruentDissection N, D'.target = T₀ ∧ D'.model = scaleTri D.model r hr.ne' := by
  obtain ⟨f, σ, hf⟩ := h
  refine ⟨relabelTarget (isoDissection f (scaleDissection D hr)) σ.symm, ?_, rfl⟩
  apply Erdos634.Realizable.Tri.ext'
  funext k
  show f (r • D.target.pts (σ.symm k)) = T₀.pts k
  have := hf (σ.symm k)
  rw [Equiv.apply_symm_apply] at this
  exact this

/-- Triangles with the same angles have proportional sides (law of sines). -/
theorem sides_prop_of_angles (T U : Tri) (h : ∀ k, T.angleAt k = U.angleAt k) :
    ∃ r : ℝ, 0 < r ∧ ∀ k, U.oppLen k = r * T.oppLen k := by
  -- `oppLen k * sin (angle at k+1) = oppLen (k+1) * sin (angle at k)`
  have hls : ∀ (V : Tri) (k : Fin 3), V.oppLen k * Real.sin (V.angleAt (k + 1)) =
      V.oppLen (k + 1) * Real.sin (V.angleAt k) := by
    intro V k
    obtain ⟨h1, h2, h3, h4⟩ := fin3_succ k
    have := EuclideanGeometry.law_sin (V.pts (k + 1)) (V.pts k) (V.pts (k + 2))
    unfold Tri.oppLen Tri.angleAt cornerAngle
    rw [h1, h2, EuclideanGeometry.angle_comm (V.pts (k + 2)) (V.pts (k + 1)) (V.pts k)]
    rw [EuclideanGeometry.angle_comm (V.pts (k + 2)) (V.pts (k + 1)) (V.pts k),
      dist_comm (V.pts (k + 2)) (V.pts (k + 1))] at this
    rw [dist_comm (V.pts (k + 2)) (V.pts k)]
    linarith
  have hsin : ∀ (V : Tri) (k : Fin 3), 0 < Real.sin (V.angleAt k) := by
    intro V k
    exact Real.sin_pos_of_pos_of_lt_pi (V.angleAt_pos' k) (by
      have := V.angleAt_sum
      have p0 := V.angleAt_pos' 0; have p1 := V.angleAt_pos' 1; have p2 := V.angleAt_pos' 2
      fin_cases k <;> simp <;> linarith)
  refine ⟨U.oppLen 0 / T.oppLen 0, div_pos (oppLen_pos U 0) (oppLen_pos T 0), fun k => ?_⟩
  have hT0 := oppLen_pos T 0
  have r1 : ∀ V : Tri, V.oppLen 1 = V.oppLen 0 * Real.sin (V.angleAt 1) / Real.sin (V.angleAt 0) := by
    intro V
    have := hls V 0
    rw [show (0 : Fin 3) + 1 = 1 from rfl] at this
    rw [eq_div_iff (hsin V 0).ne']; linarith
  have r2 : ∀ V : Tri, V.oppLen 2 = V.oppLen 0 * Real.sin (V.angleAt 2) / Real.sin (V.angleAt 0) := by
    intro V
    have := hls V 2
    rw [show (2 : Fin 3) + 1 = 0 from rfl] at this
    rw [eq_div_iff (hsin V 0).ne']; linarith
  rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) k with rfl | rfl | rfl
  · field_simp
  · rw [r1 U, r1 T, h 0, h 1]; field_simp
  · rw [r2 U, r2 T, h 0, h 2]; field_simp

/-- The scaled model has the same angles and sides multiplied by `r`. -/
theorem tileSides_scale {D : CongruentDissection N} {α β γ a b c : ℝ}
    (hT : TileSides D α β γ a b c) {r : ℝ} (hr : 0 < r) {D' : CongruentDissection N}
    (hm : D'.model = scaleTri D.model r hr.ne') :
    TileSides D' α β γ (r * a) (r * b) (r * c) := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hm, scale_angleAt, scale_oppLen _ hr, *]

/-- `s = a/c = 2 sin(α/2)`. -/
theorem s_eq {D : CongruentDissection N} {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) : a / c = 2 * Real.sin (α / 2) := by
  obtain ⟨-, -, -, -, hc, ha, -⟩ := model_facts D hrel hT
  rw [ha, mul_div_assoc, div_self hc.ne', mul_one,
    show α + β = Real.pi / 2 - α / 2 by linarith, Real.cos_pi_div_two_sub]

/-- `α` in `(0, π/3)` is determined by `2 sin(α/2)`. -/
theorem alpha_eq_of_sin {α α' : ℝ} (h0 : 0 < α) (h3 : α < Real.pi / 3) (h0' : 0 < α')
    (h3' : α' < Real.pi / 3) (h : 2 * Real.sin (α / 2) = 2 * Real.sin (α' / 2)) : α = α' := by
  have hπ := Real.pi_pos
  have := Real.injOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith : Real.sin (α / 2) = Real.sin (α' / 2))
  linarith

/-- **Transport to a triangle with the same angles.** -/
theorem transport_angles (D : CongruentDissection N) {α β γ a b c : ℝ} (hT : TileSides D α β γ a b c)
    (T₀ : Tri) (h : ∀ k, D.target.angleAt k = T₀.angleAt k) :
    ∃ (D' : CongruentDissection N) (r : ℝ) (hr : 0 < r), D'.target = T₀ ∧
      TileSides D' α β γ (r * a) (r * b) (r * c) ∧ D'.model = scaleTri D.model r hr.ne' := by
  obtain ⟨r, hr, hs⟩ := sides_prop_of_angles D.target T₀ h
  have hc : (scaleTri D.target r hr.ne').Congruent T₀ := by
    apply Erdos634.SssCongruent.congruent_of_dist
    have ho : ∀ k, (scaleTri D.target r hr.ne').oppLen k = T₀.oppLen k := by
      intro k; rw [scale_oppLen _ hr, hs]
    have hcase : ∀ i j : Fin 3, i = j ∨ ∃ k, (i = k + 1 ∧ j = k + 2) ∨ (i = k + 2 ∧ j = k + 1) := by
      decide
    intro i j
    rcases hcase i j with rfl | ⟨k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · simp
    · exact ho k
    · rw [dist_comm, dist_comm (T₀.pts _)]; exact ho k
  obtain ⟨D', h1, h2⟩ := transport D T₀ hr hc
  exact ⟨D', r, hr, h1, tileSides_scale hT hr h2, h2⟩

end TriangleTiling.ThreeAlpha
