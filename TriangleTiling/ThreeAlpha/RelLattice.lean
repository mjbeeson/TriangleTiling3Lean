/-
The rank of the relation lattice (M. Beeson, *Triangle tiling: the case 3α + 2β = π*,
arXiv 1206.2229v4): `lemma:relationlattice`.

`L` is the kernel of `v ↦ v₀ a + v₁ b + v₂ c` on `ℤ³`. Localization commutes with kernels, so
`rank_ℤ L = dim_ℚ` of the kernel on `ℚ³`, and rank-nullity over `ℚ` gives
`rank L = 3 - dim_ℚ span_ℚ {a, b, c}`.
-/
import TriangleTiling.ThreeAlpha.Relations
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.FieldTheory.Minpoly.Field

open Module

namespace TriangleTiling.ThreeAlpha

/-- The `ℤ`-linear map `v ↦ v₀ a + v₁ b + v₂ c`; its kernel is `relLattice a b c`. -/
noncomputable def relMap (a b c : ℝ) : (Fin 3 → ℤ) →ₗ[ℤ] ℝ where
  toFun v := (v 0 : ℝ) * a + v 1 * b + v 2 * c
  map_add' x y := by simp only [Pi.add_apply, Int.cast_add]; ring
  map_smul' k x := by
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, RingHom.id_apply, zsmul_eq_mul]; ring

theorem ker_relMap (a b c : ℝ) : LinearMap.ker (relMap a b c) = relLattice a b c := by
  ext v; rfl

/-- `ℤ³ → ℚ³`, a localization at the nonzero integers. -/
noncomputable abbrev castMap : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → ℚ) :=
  .pi fun i ↦ Algebra.linearMap ℤ ℚ ∘ₗ .proj i

/-- `rank L + dim_ℚ span_ℚ {a, b, c} = 3`. -/
theorem finrank_relLattice (a b c : ℝ) :
    finrank ℤ (relLattice a b c) + finrank ℚ (Submodule.span ℚ (Set.range ![a, b, c])) = 3 := by
  set p := nonZeroDivisors ℤ
  haveI : IsLocalizedModule p (LinearMap.id : ℝ →ₗ[ℤ] ℝ) := isLocalizedModule_id p ℝ ℚ
  set G := IsLocalizedModule.map p castMap LinearMap.id (relMap a b c)
  set Gext := G.extendScalarsOfIsLocalization p ℚ
  haveI := LinearMap.toKerLocalized_isLocalizedModule ℚ p castMap LinearMap.id (relMap a b c)
  have h2 := IsLocalizedModule.finrank_eq p
    (LinearMap.toKerIsLocalized p castMap LinearMap.id (relMap a b c)) le_rfl
  have h4 : finrank ℤ (LinearMap.ker G) = finrank ℚ (LinearMap.ker Gext) := by
    have := congrArg Cardinal.toNat (IsLocalization.rank_eq ℚ p le_rfl (N := LinearMap.ker Gext))
    exact this.symm
  have hH : Gext = Fintype.linearCombination ℚ ![a, b, c] := by
    apply LinearMap.pi_ext'
    intro i
    apply LinearMap.ext_ring
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single,
      Fintype.linearCombination_apply_single, one_smul]
    have : (Pi.single i (1 : ℚ) : Fin 3 → ℚ) = castMap (Pi.single i 1) := by
      ext j; by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [LinearMap.extendScalarsOfIsLocalization_apply', this, IsLocalizedModule.map_apply]
    fin_cases i <;> simp [relMap]
  have h5 := LinearMap.finrank_range_add_finrank_ker Gext
  rw [hH, Fintype.range_linearCombination] at h5
  rw [← ker_relMap, ← h2, h4, hH]
  simp only [Module.finrank_fin_fun] at h5
  omega

theorem range_three (x y z : ℝ) : Set.range ![x, y, z] = {x, y, z} := by
  ext w; simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff]

instance (x y z : ℝ) : FiniteDimensional ℚ (Submodule.span ℚ (Set.range ![x, y, z])) :=
  FiniteDimensional.span_of_finite ℚ (Set.finite_range _)

theorem dim_le_three (x y z : ℝ) : finrank ℚ (Submodule.span ℚ (Set.range ![x, y, z])) ≤ 3 := by
  have := finrank_range_le_card (R := ℚ) ![x, y, z]
  simpa only [Fintype.card_fin] using this

theorem one_le_dim {x y z : ℝ} (hz : z ≠ 0) :
    1 ≤ finrank ℚ (Submodule.span ℚ (Set.range ![x, y, z])) := by
  rw [← finrank_span_singleton (K := ℚ) hz]
  apply Submodule.finrank_mono
  rw [Submodule.span_le]
  rintro _ rfl
  exact Submodule.subset_span ⟨2, rfl⟩

theorem dim_eq_three_iff (x y z : ℝ) :
    finrank ℚ (Submodule.span ℚ (Set.range ![x, y, z])) = 3 ↔ LinearIndependent ℚ ![x, y, z] := by
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, eq_comm]
  rfl

/-- `1, s, s²` are independent over `ℚ` unless `s` is algebraic of degree at most `2`. -/
theorem linIndep_pow_iff (s : ℝ) :
    LinearIndependent ℚ ![1, s, s ^ 2] ↔ ¬ (IsAlgebraic ℚ s ∧ (minpoly ℚ s).natDegree ≤ 2) := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · rintro h ⟨halg, hdeg⟩
    have hint := halg.isIntegral
    have hm := minpoly.aeval ℚ s
    rw [Polynomial.aeval_eq_sum_range' (n := 3) (by omega)] at hm
    have h0 := h (fun i => (minpoly ℚ s).coeff i) (by
      simpa [Fin.sum_univ_three, Finset.sum_range_succ] using hm)
    apply minpoly.ne_zero hint
    ext n
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n
      · exact h0 0
      · exact h0 1
      · exact h0 2
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · intro h g hg
    by_contra hne
    push Not at hne
    obtain ⟨i, hi⟩ := hne
    set P : Polynomial ℚ := Polynomial.C (g 0) + Polynomial.C (g 1) * Polynomial.X +
      Polynomial.C (g 2) * Polynomial.X ^ 2
    have hP : P ≠ 0 := by
      intro h0
      have c0 := congrArg (Polynomial.coeff · 0) h0
      have c1 := congrArg (Polynomial.coeff · 1) h0
      have c2 := congrArg (Polynomial.coeff · 2) h0
      simp [P, Polynomial.coeff_X, Polynomial.coeff_X_pow] at c0 c1 c2
      fin_cases i
      · exact hi c0
      · exact hi c1
      · exact hi c2
    have hPs : Polynomial.aeval s P = 0 := by
      simp only [P, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_pow]
      simpa [Fin.sum_univ_three, Algebra.smul_def] using hg
    have halg : IsAlgebraic ℚ s := ⟨P, hP, hPs⟩
    apply h ⟨halg, ?_⟩
    have hd := minpoly.degree_le_of_ne_zero ℚ s hP hPs
    have hP2 : P.degree ≤ 2 := by simp only [P]; compute_degree
    exact Polynomial.natDegree_le_iff_degree_le.mpr (hd.trans hP2)

/-- The span of `x, y, z` (with `z ≠ 0`) is one-dimensional iff `x, y` are rational multiples
of `z`. -/
theorem dim_eq_one_iff {x y z : ℝ} (hz : z ≠ 0) :
    finrank ℚ (Submodule.span ℚ (Set.range ![x, y, z])) = 1 ↔
      (∃ q : ℚ, x = q * z) ∧ (∃ q : ℚ, y = q * z) := by
  set V := Submodule.span ℚ (Set.range ![x, y, z])
  have mz : z ∈ V := Submodule.subset_span ⟨2, rfl⟩
  have mx : x ∈ V := Submodule.subset_span ⟨0, rfl⟩
  have my : y ∈ V := Submodule.subset_span ⟨1, rfl⟩
  constructor
  · intro h
    have hv : (⟨z, mz⟩ : V) ≠ 0 := fun h0 => hz (congrArg Subtype.val h0)
    rw [finrank_eq_one_iff_of_nonzero' _ hv] at h
    obtain ⟨q, hq⟩ := h ⟨x, mx⟩
    obtain ⟨r, hr⟩ := h ⟨y, my⟩
    have hq' := congrArg Subtype.val hq
    have hr' := congrArg Subtype.val hr
    simp only [SetLike.val_smul, Rat.smul_def] at hq' hr'
    exact ⟨⟨q, hq'.symm⟩, ⟨r, hr'.symm⟩⟩
  · rintro ⟨⟨q, hq⟩, ⟨r, hr⟩⟩
    have hV : V = ℚ ∙ z := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_span_singleton]
        fin_cases i
        · exact ⟨q, by simp [hq, Rat.smul_def]⟩
        · exact ⟨r, by simp [hr, Rat.smul_def]⟩
        · exact ⟨1, by simp⟩
      · rw [Submodule.span_le, Set.singleton_subset_iff]; exact mz
    rw [hV]; exact finrank_span_singleton hz

theorem rationalTile_iff_dim {a b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    RationalTile a b c ↔ finrank ℚ (Submodule.span ℚ (Set.range ![a, b, c])) = 1 := by
  rw [dim_eq_one_iff hc.ne']
  constructor
  · rintro ⟨⟨q, hq⟩, ⟨r, hr⟩, -⟩
    refine ⟨⟨q, ?_⟩, ⟨r, ?_⟩⟩
    · rw [← hq]; field_simp
    · rw [← hr]; field_simp
  · rintro ⟨⟨q, hq⟩, ⟨r, hr⟩⟩
    have hr0 : (r : ℝ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hr; exact hb.ne' hr
    refine ⟨⟨q, ?_⟩, ⟨r, ?_⟩, ⟨q / r, ?_⟩⟩
    · rw [hq]; field_simp
    · rw [hr]; field_simp
    · rw [hq, hr]; push_cast; field_simp

theorem span_pow_eq (s : ℝ) :
    Submodule.span ℚ (Set.range ![-s, s ^ 2 - 1, -1]) =
      Submodule.span ℚ (Set.range ![s, s ^ 2, 1]) := by
  have m : ∀ (x y z : ℝ) (i : Fin 3), ![x, y, z] i ∈ Submodule.span ℚ (Set.range ![x, y, z]) :=
    fun x y z i => Submodule.subset_span ⟨i, rfl⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact neg_mem (m s (s ^ 2) 1 0)
    · exact sub_mem (m s (s ^ 2) 1 1) (m s (s ^ 2) 1 2)
    · exact neg_mem (m s (s ^ 2) 1 2)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · have := neg_mem (m (-s) (s ^ 2 - 1) (-1) 0)
      simpa using this
    · have := sub_mem (m (-s) (s ^ 2 - 1) (-1) 1) (m (-s) (s ^ 2 - 1) (-1) 2)
      simpa using this
    · have := neg_mem (m (-s) (s ^ 2 - 1) (-1) 2)
      simpa using this

/-- With `a = s c`, `b = (1 - s²) c`: the lattice of `(a, b, c)` is that of `(-s, s² - 1, -1)`. -/
theorem relLattice_eq {a b c s : ℝ} (hc : c ≠ 0) (ha : a = s * c) (hb : b = (1 - s ^ 2) * c) :
    relLattice a b c = relLattice (-s) (s ^ 2 - 1) (-1) := by
  ext v
  show (v 0 : ℝ) * a + v 1 * b + v 2 * c = 0 ↔ (v 0 : ℝ) * -s + v 1 * (s ^ 2 - 1) + v 2 * -1 = 0
  rw [ha, hb]
  constructor
  · intro h
    have : c * ((v 0 : ℝ) * -s + v 1 * (s ^ 2 - 1) + v 2 * -1) = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_left hc
  · intro h; linear_combination -c * h

theorem range_pow (s : ℝ) : Set.range ![1, s, s ^ 2] = Set.range ![s, s ^ 2, 1] := by
  rw [range_three, range_three]; ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

-- `0 < a` is part of the agreed statement; the proof does not need it.
set_option linter.unusedVariables false in
/-- **Lemma `lemma:relationlattice`.** `L` is a subgroup of `ℤ³` such that `kν ∈ L` for an integer
`k ≠ 0` implies `ν ∈ L`, and `rank L = 3 - dim_ℚ span_ℚ {a, b, c}`. Moreover `rank L = 2` if and
only if `T` is rational, and `rank L = 0` if and only if `a, b, c` are linearly independent over
`ℚ`. When `3α + 2β = π`, so that `a/c = s` and `b/c = 1 - s²`, a vector `(P, Q, R)` lies in `L` if
and only if `Q s² - P s - (Q + R) = 0`; hence `rank L` is `0`, `1` or `2` according as `s` has
degree at least `3` over `ℚ`, degree exactly `2`, or degree `1`.

"Degree at least 3" includes `s` transcendental. -/
theorem relationlattice {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∀ (k : ℤ) (v : Fin 3 → ℤ), k ≠ 0 → k • v ∈ relLattice a b c → v ∈ relLattice a b c) ∧
    Module.finrank ℤ (relLattice a b c)
      = 3 - Module.finrank ℚ (Submodule.span ℚ ({a, b, c} : Set ℝ)) ∧
    (Module.finrank ℤ (relLattice a b c) = 2 ↔ RationalTile a b c) ∧
    (Module.finrank ℤ (relLattice a b c) = 0 ↔ LinearIndependent ℚ ![a, b, c]) ∧
    (∀ s : ℝ, a = s * c → b = (1 - s ^ 2) * c →
      (∀ v : Fin 3 → ℤ, v ∈ relLattice a b c ↔ (v 1 : ℝ) * s ^ 2 - v 0 * s - (v 1 + v 2) = 0) ∧
      (Module.finrank ℤ (relLattice a b c) = 0 ↔
        ¬ (IsAlgebraic ℚ s ∧ (minpoly ℚ s).natDegree ≤ 2)) ∧
      (Module.finrank ℤ (relLattice a b c) = 1 ↔
        IsAlgebraic ℚ s ∧ (minpoly ℚ s).natDegree = 2) ∧
      (Module.finrank ℤ (relLattice a b c) = 2 ↔
        IsAlgebraic ℚ s ∧ (minpoly ℚ s).natDegree = 1)) := by
  have hf := finrank_relLattice a b c
  have h3 := dim_le_three a b c
  have h1 := one_le_dim (x := a) (y := b) hc.ne'
  rw [← range_three]
  refine ⟨?_, by omega, ?_, ?_, fun s hsa hsb => ?_⟩
  · intro k v hk hv
    have hv' : ((k * v 0 : ℤ) : ℝ) * a + ((k * v 1 : ℤ) : ℝ) * b + ((k * v 2 : ℤ) : ℝ) * c = 0 := hv
    show (v 0 : ℝ) * a + v 1 * b + v 2 * c = 0
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    push_cast at hv'
    have : (k : ℝ) * ((v 0 : ℝ) * a + v 1 * b + v 2 * c) = 0 := by linear_combination hv'
    exact (mul_eq_zero.mp this).resolve_left hk'
  · rw [rationalTile_iff_dim hb hc]; omega
  · rw [← dim_eq_three_iff]; omega
  · -- Reduce to the lattice of `(-s, s² - 1, -1)`, whose span is that of `1, s, s²`.
    have hL := relLattice_eq hc.ne' hsa hsb
    have hf' := finrank_relLattice (-s) (s ^ 2 - 1) (-1)
    rw [← hL, span_pow_eq, ← range_pow] at hf'
    have e3 := dim_le_three 1 s (s ^ 2)
    have e1 : 1 ≤ finrank ℚ (Submodule.span ℚ (Set.range ![1, s, s ^ 2])) := by
      rw [range_pow]; exact one_le_dim one_ne_zero
    have hthree := (dim_eq_three_iff 1 s (s ^ 2)).trans (linIndep_pow_iff s)
    have hone : finrank ℚ (Submodule.span ℚ (Set.range ![1, s, s ^ 2])) = 1 ↔
        IsAlgebraic ℚ s ∧ (minpoly ℚ s).natDegree = 1 := by
      rw [range_pow, dim_eq_one_iff one_ne_zero]
      constructor
      · rintro ⟨⟨q, hq⟩, -⟩
        have hs : s ∈ (algebraMap ℚ ℝ).range := ⟨q, by rw [hq, mul_one]; rfl⟩
        refine ⟨?_, minpoly.natDegree_eq_one_iff.mpr hs⟩
        obtain ⟨r, rfl⟩ := hs
        exact isAlgebraic_algebraMap r
      · rintro ⟨-, hd⟩
        obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.mp hd
        refine ⟨⟨q, ?_⟩, ⟨q ^ 2, ?_⟩⟩
        · rw [← hq, mul_one]; rfl
        · rw [← hq, mul_one]; push_cast; rfl
    refine ⟨fun v => ?_, ?_, ?_, ?_⟩
    · rw [hL]
      show (v 0 : ℝ) * -s + v 1 * (s ^ 2 - 1) + v 2 * -1 = 0 ↔ _
      constructor <;> intro h <;> linear_combination h
    · rw [← hthree]; omega
    · constructor
      · intro h
        have n3 : ¬ (finrank ℚ (Submodule.span ℚ (Set.range ![1, s, s ^ 2])) = 3) := by omega
        have n1 : ¬ (finrank ℚ (Submodule.span ℚ (Set.range ![1, s, s ^ 2])) = 1) := by omega
        rw [hthree, not_not] at n3
        rw [hone] at n1
        refine ⟨n3.1, ?_⟩
        have := minpoly.natDegree_pos n3.1.isIntegral
        have := n3.2
        have : (minpoly ℚ s).natDegree ≠ 1 := fun h' => n1 ⟨n3.1, h'⟩
        omega
      · rintro ⟨halg, hd⟩
        have n3 : ¬ (finrank ℚ (Submodule.span ℚ (Set.range ![1, s, s ^ 2])) = 3) := by
          rw [hthree, not_not]; exact ⟨halg, by omega⟩
        have n1 : ¬ (finrank ℚ (Submodule.span ℚ (Set.range ![1, s, s ^ 2])) = 1) := by
          rw [hone]; rintro ⟨-, h'⟩; omega
        omega
    · rw [← hone]; omega

end TriangleTiling.ThreeAlpha
