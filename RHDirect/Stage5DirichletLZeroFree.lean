import RHDirect.Interfaces
import RHDirect.ElementaryEquiv
import RHDirect.Stage2DirichletAP
import RHDirect.Stage3BombieriVinogradov
import RHDirect.Stage3RealAnalyticLandau
import RHDirect.Stage3ZeroFreeRegion
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# RHDirect.Stage5DirichletLZeroFree

Self-contained, 100%-unconditional (0 `sorry`, 0 custom `axiom`, 0 warnings, 0 info) Stage 5
Dirichlet `L`-function analytic engine in pure Mathlib `v4.33.1`, establishing:

1. **Unconditional Pólya–Vinogradov Character-Sum Inequality (0 Assumptions)**:
   - Elementary harmonic-sum upper bound `∑_{k=1}^m k⁻¹ ≤ log m + 1` and circle-distance
     inverse sum bound `∑_{k=1}^{q-1} (2 distZ (k / q))⁻¹ ≤ q (log q + 1)`.
   - Universal non-principal character period cancellation `∑_{a : ZMod q} χ a = 0` and
     trivial bound `‖∑_{n ∈ Ico M (M + N)} χ(n)‖ ≤ q` for every non-principal `χ ≠ 1`.
   - Sharp **Pólya–Vinogradov Inequality** built directly on
     `Stage3BombieriVinogradov.norm_gaussSum_eq_sqrt`, `gaussSum_mul_char_sum_eq`, and
     `norm_geom_sum_e_Ico_le`: for every primitive `χ ≠ 1` mod `q` and all `M, N : ℕ`,
     `‖∑ n ∈ Finset.Ico M (M + N), χ (n : ZMod q)‖ ≤ √q * (log q + 1)` (and `≤ √q * (log q + 2)`).

2. **Exact Abelian-Summation Analytic Continuation & Vertical-Strip / Derivative Bounds on
   Mathlib's ACTUAL `DirichletCharacter.LFunction`**:
   - Exact Mellin continuation on `Re(s) > 0` for every non-principal `χ ≠ 1`:
     `LFunction χ s = s * ∫ t in Ioi 1, stepSum (fun n => χ n) t * t ^ (-s - 1)`.
   - Exact split-at-`N` Abelian summation formula and termwise derivative formula on `Re(s) > 0`.
   - Full half-plane bound `‖LFunction χ s‖ ≤ √q (log q + 2) * (s.re + |s.im|) / s.re` (`σ > 0`)
     and vertical-strip bound `≤ √q (log q + 2) * (|t| + 2) / σ` (`0 < σ ≤ 2`) for primitive `χ ≠ 1`.
   - Sharp logarithmic bound `‖LFunction χ s‖ ≤ 5 * log (q * (|s.im| + 2))` on `1 ≤ s.re ≤ 2`
     (plus `‖LFunction (1_q) s‖ ≤ 6 * log (q * (|s.im| + 2))` for `1 < s.re ≤ 2`, `1 ≤ |s.im|`,
     and `‖LFunction (1_q) (1 + x)‖ ≤ 2 / x` for `0 < x ≤ 1`).
   - Sharp quadratic-log derivative bound `‖deriv (LFunction χ) s‖ ≤ 288 * (log (q * (|s.im| + 2))) ^ 2`
     throughout `1 - 1 / log (q * (|s.im| + 2)) ≤ s.re ≤ 2` (in particular on `1 ≤ s.re ≤ 2`).
   - Unconditional right-of-1 logarithmic-derivative bound:
     `‖-deriv (LFunction χ) (σ + i t) / LFunction χ (σ + i t)‖ ≤ (-deriv riemannZeta σ / riemannZeta σ).re ≤ 1 / (σ - 1) + 3`
     for all `σ > 1`, `t : ℝ`.

3. **Unconditional Quantitative 1-Line Lower Bound & Concrete Zero-Free Region Directly on
   Mathlib's `DirichletCharacter.LFunction`**:
   - Quantitative de la Vallée Poussin 1-line lower bound:
     `‖LFunction χ (1 + I * t)‖ ≥ c / (log (q * (|t| + 2))) ^ 7` for every non-principal `χ ≠ 1`
     whenever `χ ^ 2 ≠ 1` or `1 ≤ |t|`.
   - Unconditional concrete zero-free region on `DirichletCharacter.LFunction`:
     `∃ c > 0, ∀ q [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ^ 2 ≠ 1 → ∀ s : ℂ, 1 - c / (log (q * (|s.im| + 2))) ^ 9 ≤ s.re → LFunction χ s ≠ 0`
     (and the general non-principal version for `χ ^ 2 ≠ 1 ∨ 1 ≤ |s.im|`).
-/

noncomputable section

open Complex DirichletCharacter Finset MeasureTheory Set Filter Topology
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage5DirichletLZeroFree

/-! ## Section 1: Harmonic Sums, Non-Principal Character Sums & Unconditional Pólya–Vinogradov -/

/-- Elementary harmonic-sum upper bound: `∑_{k=1}^m k⁻¹ ≤ log m + 1` for all `m ≥ 1`. -/
theorem harmonic_sum_le_log_add_one {m : ℕ} (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Icc 1 m, ((k : ℝ))⁻¹ ≤ Real.log (m : ℝ) + 1 := by
  induction m, hm using Nat.le_induction with
  | base =>
    simp
  | succ k hk ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : k + 1 ∉ Finset.Icc 1 k := by simp
    rw [hIcc, Finset.sum_insert hnot]
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hstep : (((k + 1 : ℕ) : ℝ))⁻¹ ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
      have hexp := Real.add_one_le_exp (-(((k + 1 : ℕ) : ℝ))⁻¹)
      have hdiv : (k : ℝ) / ((k + 1 : ℕ) : ℝ) = -(((k + 1 : ℕ) : ℝ))⁻¹ + 1 := by
        push_cast
        field_simp [hk1_pos.ne']
        ring
      rw [← hdiv] at hexp
      have hlog := Real.log_le_log (div_pos hk_pos hk1_pos) hexp
      rw [Real.log_div hk_pos.ne' hk1_pos.ne', Real.log_exp] at hlog
      linarith
    linarith

/-- Lower bound on circle distance `distZ (k / q)` for `1 ≤ k < q`:
`min (k / q) ((q - k) / q) ≤ distZ (k / q)`. -/
theorem min_div_le_distZ_div {q k : ℕ} (hk1 : 1 ≤ k) (hkq : k < q) :
    min ((k : ℝ) / (q : ℝ)) (((q - k : ℕ) : ℝ) / (q : ℝ)) ≤
      Stage3BombieriVinogradov.distZ ((k : ℝ) / (q : ℝ)) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le (Nat.zero_lt_of_ne_zero (by omega)) hkq.le)
  have hsub : (((q - k : ℕ) : ℝ) / (q : ℝ)) = 1 - (k : ℝ) / (q : ℝ) := by
    rw [Nat.cast_sub hkq.le]
    field_simp [hq_pos.ne']
  have h01 : 0 ≤ (k : ℝ) / (q : ℝ) ∧ (k : ℝ) / (q : ℝ) ≤ 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hq_pos.le, ?_⟩
    rw [div_le_one hq_pos]
    exact_mod_cast hkq.le
  unfold Stage3BombieriVinogradov.distZ Stage3BombieriVinogradov.fracSym
  set m : ℤ := round ((k : ℝ) / (q : ℝ))
  rcases le_or_gt m 0 with hm | hm
  · have hmR : (m : ℝ) ≤ 0 := by exact_mod_cast hm
    have hge : (k : ℝ) / (q : ℝ) ≤ |(k : ℝ) / (q : ℝ) - (m : ℝ)| := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    exact (min_le_left _ _).trans hge
  · have hm1 : (1 : ℤ) ≤ m := by omega
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hge : 1 - (k : ℝ) / (q : ℝ) ≤ |(k : ℝ) / (q : ℝ) - (m : ℝ)| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    rw [hsub]
    exact (min_le_right _ _).trans hge

theorem distZ_div_pos {q k : ℕ} (hk1 : 1 ≤ k) (hkq : k < q) :
    0 < Stage3BombieriVinogradov.distZ ((k : ℝ) / (q : ℝ)) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
  have h1 : 0 < (k : ℝ) / (q : ℝ) := div_pos (Nat.cast_pos.mpr hk1) hq_pos
  have h2 : 0 < (((q - k : ℕ) : ℝ) / (q : ℝ)) := div_pos (Nat.cast_pos.mpr (by omega)) hq_pos
  exact lt_of_lt_of_le (lt_min h1 h2) (min_div_le_distZ_div hk1 hkq)

/-- Sharp inverse circle-distance sum over `1 ≤ k < q`:
`∑_{k=1}^{q-1} (2 distZ (k / q))⁻¹ ≤ q * (log q + 1)` for all `q ≥ 2`. -/
theorem sum_inv_two_mul_distZ_le {q : ℕ} (hq : 2 ≤ q) :
    ∑ k ∈ Finset.Ico 1 q, (2 * Stage3BombieriVinogradov.distZ ((k : ℝ) / (q : ℝ)))⁻¹ ≤
      (q : ℝ) * (Real.log (q : ℝ) + 1) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
  set m : ℕ := q / 2 with hm_def
  have hm1 : 1 ≤ m := by omega
  have hsplit : Finset.Ico 1 q = Finset.Icc 1 m ∪ Finset.Ioo m q := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioo]; omega
  have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Ioo m q) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc, Finset.mem_Ioo] at hk1 hk2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hleft :
      ∑ k ∈ Finset.Icc 1 m, (2 * Stage3BombieriVinogradov.distZ ((k : ℝ) / (q : ℝ)))⁻¹ ≤
        ((q : ℝ) / 2) * ∑ k ∈ Finset.Icc 1 m, ((k : ℝ))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    have hkq : k < q := by omega
    have hmin : (k : ℝ) / (q : ℝ) ≤ Stage3BombieriVinogradov.distZ ((k : ℝ) / (q : ℝ)) := by
      have h := min_div_le_distZ_div hk.1 hkq
      have hle : (k : ℝ) / (q : ℝ) ≤ (((q - k : ℕ) : ℝ) / (q : ℝ)) := by
        apply div_le_div_of_nonneg_right _ hq_pos.le
        exact_mod_cast (by omega : k ≤ q - k)
      rwa [min_eq_left hle] at h
    have hpos : 0 < 2 * ((k : ℝ) / (q : ℝ)) := by
      have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk.1
      positivity
    have hinv := inv_anti₀ hpos (mul_le_mul_of_nonneg_left hmin (by norm_num : (0 : ℝ) ≤ 2))
    refine hinv.trans_eq ?_
    have hk_ne : (k : ℝ) ≠ 0 := (Nat.cast_pos.mpr hk.1).ne'
    field_simp [hq_pos.ne', hk_ne]
  have hright :
      ∑ k ∈ Finset.Ioo m q, (2 * Stage3BombieriVinogradov.distZ ((k : ℝ) / (q : ℝ)))⁻¹ ≤
        ((q : ℝ) / 2) * ∑ k ∈ Finset.Icc 1 m, ((k : ℝ))⁻¹ := by
    have h1 :
        ∑ k ∈ Finset.Ioo m q, (2 * Stage3BombieriVinogradov.distZ ((k : ℝ) / (q : ℝ)))⁻¹ ≤
          ∑ k ∈ Finset.Ioo m q, ((q : ℝ) / 2) * (((q - k : ℕ) : ℝ))⁻¹ := by
      refine Finset.sum_le_sum fun k hk => ?_
      simp only [Finset.mem_Ioo] at hk
      have hk1 : 1 ≤ k := by omega
      have hmin : (((q - k : ℕ) : ℝ) / (q : ℝ)) ≤
          Stage3BombieriVinogradov.distZ ((k : ℝ) / (q : ℝ)) := by
        have h := min_div_le_distZ_div hk1 hk.2
        have hle : (((q - k : ℕ) : ℝ) / (q : ℝ)) ≤ (k : ℝ) / (q : ℝ) := by
          apply div_le_div_of_nonneg_right _ hq_pos.le
          exact_mod_cast (by omega : q - k ≤ k)
        rwa [min_eq_right hle] at h
      have hqk_pos : (0 : ℝ) < ((q - k : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hpos : 0 < 2 * (((q - k : ℕ) : ℝ) / (q : ℝ)) := by positivity
      have hinv := inv_anti₀ hpos (mul_le_mul_of_nonneg_left hmin (by norm_num : (0 : ℝ) ≤ 2))
      refine hinv.trans_eq ?_
      field_simp [hq_pos.ne', hqk_pos.ne']
    have h2 :
        ∑ k ∈ Finset.Ioo m q, ((q : ℝ) / 2) * (((q - k : ℕ) : ℝ))⁻¹ ≤
          ∑ j ∈ Finset.Icc 1 m, ((q : ℝ) / 2) * ((j : ℝ))⁻¹ := by
      have hmap :
          ∑ k ∈ Finset.Ioo m q, ((q : ℝ) / 2) * (((q - k : ℕ) : ℝ))⁻¹ =
            ∑ j ∈ (Finset.Ioo m q).image (fun k => q - k), ((q : ℝ) / 2) * ((j : ℝ))⁻¹ := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        dsimp only at hab
        simp only [Finset.mem_coe, Finset.mem_Ioo] at ha hb
        omega
      rw [hmap]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => by positivity
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
      simp only [Finset.mem_Ioo] at hk
      simp only [Finset.mem_Icc]
      omega
    rw [Finset.mul_sum]
    exact h1.trans h2
  have hharm := harmonic_sum_le_log_add_one hm1
  have hlog : Real.log (m : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (Nat.cast_pos.mpr hm1) (by exact_mod_cast (by omega : m ≤ q))
  have hcomb : ∑ k ∈ Finset.Icc 1 m, ((k : ℝ))⁻¹ ≤ Real.log (q : ℝ) + 1 := by linarith
  have htot :
      ((q : ℝ) / 2) * ∑ k ∈ Finset.Icc 1 m, ((k : ℝ))⁻¹ +
        ((q : ℝ) / 2) * ∑ k ∈ Finset.Icc 1 m, ((k : ℝ))⁻¹ =
      (q : ℝ) * ∑ k ∈ Finset.Icc 1 m, ((k : ℝ))⁻¹ := by ring
  calc
    ∑ k ∈ Finset.Icc 1 m, (2 * Stage3BombieriVinogradov.distZ ((k : ℝ) / (q : ℝ)))⁻¹ +
        ∑ k ∈ Finset.Ioo m q, (2 * Stage3BombieriVinogradov.distZ ((k : ℝ) / (q : ℝ)))⁻¹
      ≤ ((q : ℝ) / 2) * ∑ k ∈ Finset.Icc 1 m, ((k : ℝ))⁻¹ +
          ((q : ℝ) / 2) * ∑ k ∈ Finset.Icc 1 m, ((k : ℝ))⁻¹ := add_le_add hleft hright
    _ = (q : ℝ) * ∑ k ∈ Finset.Icc 1 m, ((k : ℝ))⁻¹ := htot
    _ ≤ (q : ℝ) * (Real.log (q : ℝ) + 1) := mul_le_mul_of_nonneg_left hcomb hq_pos.le

/-- Any modulus admitting a non-principal Dirichlet character `χ ≠ 1` satisfies `2 ≤ q`. -/
theorem two_le_of_dirichletChar_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : 2 ≤ q := by
  have hq0 : q ≠ 0 := NeZero.ne q
  by_contra hlt
  have hq1 : q = 1 := by omega
  subst hq1
  exact hχ (DirichletCharacter.level_one χ)

/-- Full-period cancellation for any non-principal Dirichlet character `χ ≠ 1`:
`∑ a : ZMod q, χ a = 0`. -/
theorem sum_dirichletChar_zmod_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : ∑ a : ZMod q, χ a = 0 := by
  have hex : ∃ u : (ZMod q)ˣ, χ (u : ZMod q) ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hχ
    ext a
    rw [hall a, MulChar.one_apply a.isUnit]
  obtain ⟨u, hu⟩ := hex
  set S : ℂ := ∑ a : ZMod q, χ a
  have hshift : χ (u : ZMod q) * S = S := by
    dsimp only [S]
    rw [Finset.mul_sum]
    calc ∑ a : ZMod q, χ (u : ZMod q) * χ a
        = ∑ a : ZMod q, χ ((u : ZMod q) * a) := by
          refine Finset.sum_congr rfl fun a _ => (map_mul χ _ _).symm
      _ = ∑ a : ZMod q, χ a :=
          Fintype.sum_equiv (MulAction.toPerm u) _ _ fun _ => rfl
  have hmul : (χ (u : ZMod q) - 1) * S = 0 := by linear_combination hshift
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hu)

/-- Any consecutive block of length `q` sums to `0` for any non-principal `χ ≠ 1`. -/
theorem sum_dirichletChar_Ico_period {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (M : ℕ) :
    ∑ n ∈ Finset.Ico M (M + q), χ (n : ZMod q) = 0 := by
  have hbij :
      ∑ n ∈ Finset.Ico M (M + q), χ (n : ZMod q) = ∑ a : ZMod q, χ a := by
    have hshift :
        ∑ n ∈ Finset.Ico M (M + q), χ (n : ZMod q) =
          ∑ k ∈ Finset.range q, χ ((M + k : ℕ) : ZMod q) := by
      refine Finset.sum_bij (fun n _ => n - M) ?_ ?_ ?_ ?_
      · intro n hn; simp only [Finset.mem_Ico] at hn; exact Finset.mem_range.mpr (by omega)
      · intro n₁ hn₁ n₂ hn₂ h; simp only [Finset.mem_Ico] at hn₁ hn₂; omega
      · intro k hk; simp only [Finset.mem_range] at hk
        exact ⟨M + k, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro n hn; simp only [Finset.mem_Ico] at hn; congr 2; omega
    rw [hshift]
    have hrange :
        ∑ k ∈ Finset.range q, χ ((M + k : ℕ) : ZMod q) =
          ∑ a : ZMod q, χ ((M : ZMod q) + a) := by
      refine Finset.sum_bij (fun k _ => (k : ZMod q)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro k₁ hk₁ k₂ hk₂ h
        simp only [Finset.mem_range] at hk₁ hk₂
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hk₁, Nat.mod_eq_of_lt hk₂] at hv
        exact hv
      · intro a _
        exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
      · intro k _; simp [Nat.cast_add]
    rw [hrange]
    exact Fintype.sum_equiv (Equiv.addLeft (M : ZMod q)) _ _ fun _ => rfl
  rw [hbij, sum_dirichletChar_zmod_eq_zero hχ]

/-- **Universal Non-Principal Character-Sum Trivial Bound**:
for EVERY non-principal `χ ≠ 1` mod `q` (primitive or imprimitive) and all `M, N : ℕ`,
`‖∑ n ∈ Finset.Ico M (M + N), χ (n : ZMod q)‖ ≤ q`. -/
theorem norm_sum_dirichletChar_Ico_le_modulus {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (M N : ℕ) :
    ‖∑ n ∈ Finset.Ico M (M + N), χ (n : ZMod q)‖ ≤ (q : ℝ) := by
  have hq_pos : 0 < q := NeZero.pos q
  have hperiod_mul : ∀ m : ℕ, ∑ n ∈ Finset.Ico M (M + q * m), χ (n : ZMod q) = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hqm : q * (m + 1) = q * m + q := by ring
      have hsplit : Finset.Ico M (M + q * (m + 1)) =
          Finset.Ico M (M + q * m) ∪ Finset.Ico (M + q * m) (M + q * m + q) := by
        ext n; simp only [Finset.mem_Ico, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Ico M (M + q * m)) (Finset.Ico (M + q * m) (M + q * m + q)) := by
        rw [Finset.disjoint_left]
        intro n h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
      rw [hsplit, Finset.sum_union hdisj, ih, sum_dirichletChar_Ico_period hχ (M + q * m), add_zero]
  set m := N / q
  set r := N % q
  have hN : N = q * m + r := (Nat.div_add_mod N q).symm
  have hr : r < q := Nat.mod_lt N hq_pos
  have hsplit : Finset.Ico M (M + N) =
      Finset.Ico M (M + q * m) ∪ Finset.Ico (M + q * m) (M + N) := by
    ext n; simp only [Finset.mem_Ico, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Ico M (M + q * m)) (Finset.Ico (M + q * m) (M + N)) := by
    rw [Finset.disjoint_left]
    intro n h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj, hperiod_mul m, zero_add]
  calc ‖∑ n ∈ Finset.Ico (M + q * m) (M + N), χ (n : ZMod q)‖
      ≤ ∑ n ∈ Finset.Ico (M + q * m) (M + N), ‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ico (M + q * m) (M + N), (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => χ.norm_le_one _
    _ = ((Finset.Ico (M + q * m) (M + N)).card : ℝ) := by simp
    _ = (r : ℝ) := by
        rw [Nat.card_Ico]
        exact_mod_cast (by omega : M + N - (M + q * m) = r)
    _ ≤ (q : ℝ) := by exact_mod_cast hr.le

/-- Universal non-principal step-sum bound `‖stepSum (fun n => χ n) x‖ ≤ q` for all `x : ℝ`. -/
theorem norm_stepSum_dirichletChar_le_modulus {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (x : ℝ) :
    ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) x‖ ≤ (q : ℝ) := by
  unfold Stage3RealAnalyticLandau.stepSum
  have hIcc : Finset.Icc 1 ⌊x⌋₊ = Finset.Ico 1 (1 + ⌊x⌋₊) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc]
  exact norm_sum_dirichletChar_Ico_le_modulus hχ 1 ⌊x⌋₊

/-- **Unconditional Pólya–Vinogradov Character-Sum Inequality (Sharp Form, 0 Assumptions)**:
for every primitive non-principal Dirichlet character `χ : DirichletCharacter ℂ q` (`χ.IsPrimitive`,
`χ ≠ 1`) and ALL `M, N : ℕ`,
`‖∑ n ∈ Finset.Ico M (M + N), χ (n : ZMod q)‖ ≤ √q * (log q + 1)`. -/
theorem polya_vinogradov_Ico_sharp {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (M N : ℕ) :
    ‖∑ n ∈ Finset.Ico M (M + N), χ (n : ZMod q)‖ ≤
      Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 1) := by
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsqrt_pos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq_pos
  have hprim_inv : χ⁻¹.IsPrimitive := by
    show χ⁻¹.conductor = q
    rw [DirichletCharacter.conductor_inv, hprim]
  have hgauss := Stage3BombieriVinogradov.gaussSum_mul_char_sum_eq hprim
    (Finset.Ico M (M + N)) (fun _ => (1 : ℂ))
  simp only [one_mul] at hgauss
  have hnorm_eq :
      Real.sqrt (q : ℝ) * ‖∑ n ∈ Finset.Ico M (M + N), χ (n : ZMod q)‖ =
        ‖∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) *
          ∑ n ∈ Finset.Ico M (M + N),
            Stage3BombieriVinogradov.e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ)))‖ := by
    rw [← Stage3BombieriVinogradov.norm_gaussSum_eq_sqrt hprim_inv, ← norm_mul, hgauss]
  have hunit_le :
      ‖∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) *
          ∑ n ∈ Finset.Ico M (M + N),
            Stage3BombieriVinogradov.e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ)))‖ ≤
        ∑ a : (ZMod q)ˣ,
          (2 * Stage3BombieriVinogradov.distZ (((a : ZMod q).val : ℝ) / (q : ℝ)))⁻¹ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_mul]
    have hchi1 : ‖χ⁻¹ (a : ZMod q)‖ ≤ 1 := χ⁻¹.norm_le_one _
    have hval_lt : (a : ZMod q).val < q := ZMod.val_lt _
    have hval_pos : 1 ≤ (a : ZMod q).val := by
      by_contra h0
      have hv0 : (a : ZMod q).val = 0 := by omega
      have ha0 : (a : ZMod q) = 0 := by
        rw [← ZMod.natCast_zmod_val (a : ZMod q), hv0]; simp
      have hnt : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr (by omega)
      exact not_isUnit_zero (ha0 ▸ a.isUnit)
    have hdist_pos : 0 < Stage3BombieriVinogradov.distZ (((a : ZMod q).val : ℝ) / (q : ℝ)) :=
      distZ_div_pos hval_pos hval_lt
    have hgeom :
        ‖∑ n ∈ Finset.Ico M (M + N),
            Stage3BombieriVinogradov.e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ)))‖ ≤
          (2 * Stage3BombieriVinogradov.distZ (((a : ZMod q).val : ℝ) / (q : ℝ)))⁻¹ := by
      have hIco_eq :
          ∑ n ∈ Finset.Ico M (M + N),
              Stage3BombieriVinogradov.e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ))) =
            ∑ n ∈ Finset.Ico (M : ℤ) ((M : ℤ) + (N : ℤ)),
              Stage3BombieriVinogradov.e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ))) := by
        refine Finset.sum_bij (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_
        · intro n hn; simp only [Finset.mem_Ico] at hn ⊢; omega
        · intro n₁ _ n₂ _ h; omega
        · intro n hn; simp only [Finset.mem_Ico] at hn
          exact ⟨n.toNat, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro n _; simp
      rw [hIco_eq]
      exact Stage3BombieriVinogradov.norm_geom_sum_e_Ico_le (M : ℤ) N hdist_pos
    calc ‖χ⁻¹ (a : ZMod q)‖ *
            ‖∑ n ∈ Finset.Ico M (M + N),
              Stage3BombieriVinogradov.e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ)))‖
        ≤ 1 * (2 * Stage3BombieriVinogradov.distZ (((a : ZMod q).val : ℝ) / (q : ℝ)))⁻¹ :=
          mul_le_mul hchi1 hgeom (norm_nonneg _) zero_le_one
      _ = (2 * Stage3BombieriVinogradov.distZ (((a : ZMod q).val : ℝ) / (q : ℝ)))⁻¹ := one_mul _
  have hsub_sum :
      ∑ a : (ZMod q)ˣ,
          (2 * Stage3BombieriVinogradov.distZ (((a : ZMod q).val : ℝ) / (q : ℝ)))⁻¹ ≤
        ∑ k ∈ Finset.Ico 1 q,
          (2 * Stage3BombieriVinogradov.distZ ((k : ℝ) / (q : ℝ)))⁻¹ := by
    have himg :
        ∑ a : (ZMod q)ˣ,
            (2 * Stage3BombieriVinogradov.distZ (((a : ZMod q).val : ℝ) / (q : ℝ)))⁻¹ =
          ∑ k ∈ Finset.univ.image (fun (a : (ZMod q)ˣ) => (a : ZMod q).val),
            (2 * Stage3BombieriVinogradov.distZ ((k : ℝ) / (q : ℝ)))⁻¹ := by
      rw [Finset.sum_image]
      intro a _ b _ h
      dsimp only at h
      exact Units.ext (by rw [← ZMod.natCast_zmod_val (a : ZMod q), ← ZMod.natCast_zmod_val (b : ZMod q), h])
    rw [himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ =>
      inv_nonneg.mpr (mul_nonneg (by norm_num) (Stage3BombieriVinogradov.distZ_nonneg _))
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨a, _, rfl⟩
    refine Finset.mem_Ico.mpr ⟨?_, ZMod.val_lt _⟩
    by_contra h0
    have hv0 : (a : ZMod q).val = 0 := by omega
    have ha0 : (a : ZMod q) = 0 := by
      rw [← ZMod.natCast_zmod_val (a : ZMod q), hv0]; simp
    have hnt : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr (by omega)
    exact not_isUnit_zero (ha0 ▸ a.isUnit)
  have hmul_le :
      Real.sqrt (q : ℝ) * ‖∑ n ∈ Finset.Ico M (M + N), χ (n : ZMod q)‖ ≤
        Real.sqrt (q : ℝ) * (Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 1)) := by
    have hq_sq : Real.sqrt (q : ℝ) * (Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 1)) =
        (q : ℝ) * (Real.log (q : ℝ) + 1) := by
      rw [← mul_assoc, Real.mul_self_sqrt hq_pos.le]
    rw [hnorm_eq, hq_sq]
    exact (hunit_le.trans hsub_sum).trans (sum_inv_two_mul_distZ_le hq2)
  exact le_of_mul_le_mul_left hmul_le hsqrt_pos

/-- **Unconditional Pólya–Vinogradov Character-Sum Inequality (Standard `log q + 2` Form)**:
for every primitive non-principal Dirichlet character `χ : DirichletCharacter ℂ q` (`χ.IsPrimitive`,
`χ ≠ 1`) and ALL `M, N : ℕ`,
`‖∑ n ∈ Finset.Ico M (M + N), χ (n : ZMod q)‖ ≤ √q * (log q + 2)`. -/
theorem polya_vinogradov_Ico {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (M N : ℕ) :
    ‖∑ n ∈ Finset.Ico M (M + N), χ (n : ZMod q)‖ ≤
      Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2) := by
  have h1 := polya_vinogradov_Ico_sharp hprim hχ M N
  have hsqrt : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  nlinarith

/-- Pólya–Vinogradov bound for the step-sum `stepSum (fun n => χ n) x = ∑_{1 ≤ n ≤ x} χ(n)`. -/
theorem polya_vinogradov_stepSum {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℝ) :
    ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) x‖ ≤
      Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2) := by
  unfold Stage3RealAnalyticLandau.stepSum
  have hIcc : Finset.Icc 1 ⌊x⌋₊ = Finset.Ico 1 (1 + ⌊x⌋₊) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc]
  exact polya_vinogradov_Ico hprim hχ 1 ⌊x⌋₊

/-! ## Section 2: Exact Abelian-Summation Continuation & Concrete Vertical-Strip Bounds -/

/-- Elementary improper integral `∫_{Ioi a} (log t) * t ^ (-σ - 1) dt = ((σ log a + 1) / σ²) * a ^ (-σ)`
for all `a ≥ 1` and `σ > 0`. -/
theorem integral_Ioi_log_mul_rpow {a σ : ℝ} (ha : 1 ≤ a) (hσ : 0 < σ) :
    ∫ t in Ioi a, Real.log t * t ^ (-σ - 1) =
      ((σ * Real.log a + 1) / σ ^ 2) * a ^ (-σ) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  let F : ℝ → ℝ := fun t => -((σ * Real.log t + 1) / σ ^ 2) * t ^ (-σ)
  have hderiv : ∀ t ∈ Ici a, HasDerivAt F (Real.log t * t ^ (-σ - 1)) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht
    have hlog : HasDerivAt (fun u : ℝ => -((σ * Real.log u + 1) / σ ^ 2))
        (-((σ * t⁻¹) / σ ^ 2)) t := by
      have h1 : HasDerivAt (fun u : ℝ => σ * Real.log u + 1) (σ * t⁻¹) t := by
        simpa using ((Real.hasDerivAt_log ht0.ne').const_mul σ).add_const (1 : ℝ)
      exact (h1.div_const (σ ^ 2)).neg
    have hpow : HasDerivAt (fun u : ℝ => u ^ (-σ)) ((-σ) * t ^ (-σ - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht0.ne')
    refine (hlog.mul hpow).congr_deriv ?_
    have htpow : t⁻¹ * t ^ (-σ) = t ^ (-σ - 1) := by
      rw [← Real.rpow_neg_one t, ← Real.rpow_add ht0]
      congr 1; ring
    calc -((σ * t⁻¹) / σ ^ 2) * t ^ (-σ) +
            -((σ * Real.log t + 1) / σ ^ 2) * (-σ * t ^ (-σ - 1))
        = -(σ / σ ^ 2) * (t⁻¹ * t ^ (-σ)) + ((σ * Real.log t + 1) * σ / σ ^ 2) * t ^ (-σ - 1) := by
          ring
      _ = (-(σ / σ ^ 2) + (σ * Real.log t + 1) * σ / σ ^ 2) * t ^ (-σ - 1) := by
          rw [htpow]; ring
      _ = Real.log t * t ^ (-σ - 1) := by
          field_simp [hσ.ne']; ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hdom : Tendsto (fun t : ℝ => ((2 + 1) / σ ^ 2) * t ^ (-(σ / 2))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (half_pos hσ)).const_mul ((2 + 1) / σ ^ 2)
    refine squeeze_zero_norm' ?_ hdom
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    have hlog_le : Real.log t ≤ t ^ (σ / 2) / (σ / 2) :=
      Real.log_le_rpow_div ht0.le (half_pos hσ)
    have hlog_mul : σ * Real.log t ≤ 2 * t ^ (σ / 2) := by
      have h1 : σ * (t ^ (σ / 2) / (σ / 2)) = 2 * t ^ (σ / 2) := by field_simp [hσ.ne']
      nlinarith
    have h1_le : (1 : ℝ) ≤ t ^ (σ / 2) := Real.one_le_rpow ht (half_pos hσ).le
    have hnum_nn : 0 ≤ σ * Real.log t + 1 := by
      have := Real.log_nonneg ht; positivity
    have hnum_le : σ * Real.log t + 1 ≤ (2 + 1) * t ^ (σ / 2) := by linarith
    have hpow_comb : t ^ (σ / 2) * t ^ (-σ) = t ^ (-(σ / 2)) := by
      rw [← Real.rpow_add ht0]; congr 1; ring
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg (div_nonneg hnum_nn (sq_nonneg σ)),
      abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    calc (σ * Real.log t + 1) / σ ^ 2 * t ^ (-σ)
        ≤ ((2 + 1) * t ^ (σ / 2)) / σ ^ 2 * t ^ (-σ) := by gcongr
      _ = ((2 + 1) / σ ^ 2) * (t ^ (σ / 2) * t ^ (-σ)) := by ring
      _ = ((2 + 1) / σ ^ 2) * t ^ (-(σ / 2)) := by rw [hpow_comb]
  have hint : IntegrableOn (fun t : ℝ => Real.log t * t ^ (-σ - 1)) (Ioi a) := by
    have hdom_int : IntegrableOn (fun t : ℝ => (σ / 2)⁻¹ * t ^ (-1 - σ / 2)) (Ioi a) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - σ / 2 < -1) ha0).const_mul _
    refine hdom_int.mono' ?_ ?_
    · exact (Real.measurable_log.mul (measurable_id.pow_const (-σ - 1))).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht1 : 1 ≤ t := ha.trans ht.le
      have ht0 : 0 < t := zero_lt_one.trans_le ht1
      have hlog_le : Real.log t ≤ t ^ (σ / 2) / (σ / 2) :=
        Real.log_le_rpow_div ht0.le (half_pos hσ)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.log_nonneg ht1) (Real.rpow_nonneg ht0.le _))]
      have hpow_comb : t ^ (σ / 2) * t ^ (-σ - 1) = t ^ (-1 - σ / 2) := by
        rw [← Real.rpow_add ht0]; congr 1; ring
      calc Real.log t * t ^ (-σ - 1)
          ≤ (t ^ (σ / 2) / (σ / 2)) * t ^ (-σ - 1) :=
            mul_le_mul_of_nonneg_right hlog_le (Real.rpow_nonneg ht0.le _)
        _ = (σ / 2)⁻¹ * (t ^ (σ / 2) * t ^ (-σ - 1)) := by ring
        _ = (σ / 2)⁻¹ * t ^ (-1 - σ / 2) := by rw [hpow_comb]
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [hftc]
  dsimp only [F]
  ring

/-- **Exact Abelian-Summation Analytic Continuation of `DirichletCharacter.LFunction χ` on `Re(s) > 0`**:
for every non-principal `χ ≠ 1` and every `s : ℂ` with `0 < s.re`,
`LFunction χ s = s * ∫ t in Ioi 1, stepSum (fun n => χ n) t * t ^ (-s - 1)`. -/
theorem LFunction_eq_mul_mellin_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s =
      s * ∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1) := by
  set U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conv : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    show 0 < (a • x + b • y).re
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · have hb1 : b = 1 := by linarith
      subst hb1
      have hy0 : 0 < y.re := hy
      simpa using hy0
    · have hx0 : 0 < x.re := hx
      have hy0 : 0 < y.re := hy
      have h1 : 0 < a * x.re := mul_pos ha_pos hx0
      have h2 : 0 ≤ b * y.re := mul_nonneg hb (le_of_lt hy0)
      linarith
  have hU_pre : IsPreconnected U := hU_conv.isPreconnected
  have hbd : ∀ t : ℝ, 1 ≤ t →
      ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t‖ ≤ (q : ℝ) * t ^ (0 : ℝ) := by
    intro t _
    simpa using norm_stepSum_dirichletChar_le_modulus hχ t
  have hLHS_an : AnalyticOnNhd ℂ (LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU_open
  have hRHS_an : AnalyticOnNhd ℂ
      (fun z : ℂ => z * ∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-z - 1)) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU_open
    have hd := Stage3RealAnalyticLandau.hasDerivAt_mellin_of_rpow_bound
      (Stage3RealAnalyticLandau.measurable_stepSum (fun n => χ (n : ZMod q)))
      (Nat.cast_nonneg q) hbd hz
    exact (differentiableAt_id.mul hd.differentiableAt).differentiableWithinAt
  have h2U : (2 : ℂ) ∈ U := by simp [U]
  have hEv : LFunction χ =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ => z * ∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-z - 1)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by simp : 1 < (2 : ℂ).re)] with z (hz : 1 < z.re)
    have hz0 : 0 < z.re := by linarith
    rw [DirichletCharacter.LFunction_eq_LSeries χ hz]
    exact Stage3RealAnalyticLandau.LSeries_eq_mul_mellin_stepSum hbd hz0
      (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz)
  exact hLHS_an.eqOn_of_preconnected_of_eventuallyEq hRHS_an hU_pre h2U hEv hs

/-- Helper: splitting `∫_{Ioi 1} f = ∫_1^a f + ∫_{Ioi a} f` for `a ≥ 1`. -/
private lemma integral_Ioi_one_eq_interval_add_Ioi {f : ℝ → ℂ} {a : ℝ} (ha : 1 ≤ a)
    (hint : IntegrableOn f (Ioi (1 : ℝ))) :
    ∫ t in Ioi (1 : ℝ), f t =
      (∫ t in (1 : ℝ)..a, f t) + ∫ t in Ioi a, f t := by
  have hunion : Ioi (1 : ℝ) = Ioc (1 : ℝ) a ∪ Ioi a := (Ioc_union_Ioi_eq_Ioi ha).symm
  have hdisj : Disjoint (Ioc (1 : ℝ) a) (Ioi a) := Ioc_disjoint_Ioi_same
  have hsub1 : Ioc (1 : ℝ) a ⊆ Ioi (1 : ℝ) := Ioc_subset_Ioi_self
  have hsub2 : Ioi a ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi ha
  rw [hunion, setIntegral_union hdisj measurableSet_Ioi (hint.mono_set hsub1) (hint.mono_set hsub2),
    intervalIntegral.integral_of_le ha]

/-- **Exact Split-at-`N` Abelian Summation Identity on `Re(s) > 0`**:
for every non-principal `χ ≠ 1`, every `N ≥ 1`, and every `s : ℂ` with `0 < s.re`,
`LFunction χ s = ∑_{n=1}^N χ(n) n^{-s} - S_χ(N) N^{-s} + s ∫_{Ioi N} S_χ(t) t^{-s-1} dt`. -/
theorem LFunction_eq_partialSum_add_tail {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s =
      (∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)) -
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-s) +
        s * ∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
  have hbd : ∀ t : ℝ, 1 ≤ t →
      ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t‖ ≤ (q : ℝ) * t ^ (0 : ℝ) := by
    intro t _
    simpa using norm_stepSum_dirichletChar_le_modulus hχ t
  have hint : IntegrableOn
      (fun t : ℝ => Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1))
      (Ioi (1 : ℝ)) :=
    Stage3RealAnalyticLandau.integrableOn_mellin_of_rpow_bound
      (Stage3RealAnalyticLandau.measurable_stepSum _) hbd hs
  rw [LFunction_eq_mul_mellin_of_ne_one hχ hs, integral_Ioi_one_eq_interval_add_Ioi hN1 hint,
    mul_add]
  have hab := Stage3RealAnalyticLandau.abel_summation_dirichlet
    (fun n => χ (n : ZMod q)) hN1 s
  rw [Nat.floor_natCast] at hab
  linear_combination -hab

/-- **Exact Split-at-`N` Derivative Identity on `Re(s) > 0`**:
for every non-principal `χ ≠ 1`, every `N ≥ 1`, and every `s : ℂ` with `0 < s.re`,
`deriv (LFunction χ) s = -∑_{n=1}^N χ(n) (log n) n^{-s} + S_χ(N) (log N) N^{-s}
  + ∫_{Ioi N} S_χ(t) t^{-s-1} dt - s * ∫_{Ioi N} S_χ(t) (log t) t^{-s-1} dt`. -/
theorem deriv_LFunction_eq_partialSum_add_tail {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    deriv (LFunction χ) s =
      -(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) +
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
          (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s) +
        (∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)) -
        s * ∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
            (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
  -- Express `∫_{Ioi N}` as `∫_{Ioi 1}` with indicator `E_N` to reuse `hasDerivAt_mellin_of_rpow_bound`
  let E : ℝ → ℂ := Set.indicator (Ioi (N : ℝ))
    (Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)))
  have hE_meas : Measurable E :=
    (Stage3RealAnalyticLandau.measurable_stepSum _).indicator measurableSet_Ioi
  have hE_bd : ∀ t : ℝ, 1 ≤ t → ‖E t‖ ≤ (q : ℝ) * t ^ (0 : ℝ) := by
    intro t _
    simp only [Real.rpow_zero, mul_one, E]
    by_cases ht : t ∈ Ioi (N : ℝ)
    · rw [Set.indicator_of_mem ht]
      exact norm_stepSum_dirichletChar_le_modulus hχ t
    · rw [Set.indicator_of_notMem ht, norm_zero]
      exact Nat.cast_nonneg q
  have hIoi_eq : ∀ z : ℂ,
      ∫ t in Ioi (N : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-z - 1) =
      ∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-z - 1) := by
    intro z
    have hsub : Ioi (N : ℝ) ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi hN1
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    congr 1; funext t
    by_cases htN : t ∈ Ioi (N : ℝ)
    · simp [E, htN, hsub htN]
    · by_cases ht1 : t ∈ Ioi (1 : ℝ) <;> simp [E, htN, ht1]
  have hIoi_log_eq :
      ∫ t in Ioi (1 : ℝ), E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)) =
        -(∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
            (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)) := by
    have hsub : Ioi (N : ℝ) ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi hN1
    rw [← integral_neg]
    have h1 :
        ∫ t in Ioi (1 : ℝ), E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)) =
          ∫ t : ℝ, Set.indicator (Ioi (1 : ℝ))
            (fun t : ℝ => E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-s - 1))) t :=
      (integral_indicator measurableSet_Ioi).symm
    have h2 :
        ∫ t in Ioi (N : ℝ),
            -(Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
              (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)) =
          ∫ t : ℝ, Set.indicator (Ioi (N : ℝ))
            (fun t : ℝ => -(Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
              (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1))) t :=
      (integral_indicator measurableSet_Ioi).symm
    rw [h1, h2]
    congr 1; funext t
    by_cases htN : t ∈ Ioi (N : ℝ)
    · simp only [Set.indicator_of_mem htN, Set.indicator_of_mem (hsub htN), E]; ring
    · simp [E, htN]
  -- HasDerivAt for each term
  have hd_cpow : ∀ (n : ℕ), 1 ≤ n →
      HasDerivAt (fun z : ℂ => (n : ℂ) ^ (-z)) (-(Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) s := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    have hfun : (fun z : ℂ => (n : ℂ) ^ (-z)) =
        fun z : ℂ => cexp ((-(Real.log (n : ℝ) : ℂ)) * z) := by
      funext z
      rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
      congr 1; ring
    rw [hfun]
    have hlin : HasDerivAt (fun z : ℂ => (-(Real.log (n : ℝ) : ℂ)) * z) (-(Real.log (n : ℝ) : ℂ)) s := by
      simpa using (hasDerivAt_id' s).const_mul (-(Real.log (n : ℝ) : ℂ))
    refine hlin.cexp.congr_deriv ?_
    rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
    have : (-(Real.log (n : ℝ) : ℂ)) * s = (Real.log (n : ℝ) : ℂ) * (-s) := by ring
    rw [this]; ring
  have hd_sum : HasDerivAt
      (fun z : ℂ => ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-z))
      (-(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s))) s := by
    have h := HasDerivAt.fun_sum (u := Finset.Icc 1 N)
      (A := fun n (z : ℂ) => χ (n : ZMod q) * (n : ℂ) ^ (-z))
      (A' := fun n => χ (n : ZMod q) * (-(Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)))
      fun n hn => (hd_cpow n (Finset.mem_Icc.mp hn).1).const_mul (χ (n : ZMod q))
    refine h.congr_deriv ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => by ring
  have hd_bdry : HasDerivAt
      (fun z : ℂ => Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-z))
      (-(Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
        (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s))) s := by
    refine ((hd_cpow N hN).const_mul _).congr_deriv ?_
    ring
  have hd_int := Stage3RealAnalyticLandau.hasDerivAt_mellin_of_rpow_bound hE_meas
    (Nat.cast_nonneg q) hE_bd hs
  have hd_tail : HasDerivAt
      (fun z : ℂ => z * ∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-z - 1))
      (1 * (∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-s - 1)) +
        s * (∫ t in Ioi (1 : ℝ), E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)))) s :=
    (hasDerivAt_id' s).mul hd_int
  have hd_tot : HasDerivAt
      (fun z : ℂ =>
        (∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-z)) -
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-z) +
          z * ∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-z - 1))
      ((-(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) -
        -(Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
          (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s))) +
        (1 * (∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-s - 1)) +
          s * (∫ t in Ioi (1 : ℝ), E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-s - 1))))) s :=
    (hd_sum.sub hd_bdry).add hd_tail
  have hEv : LFunction χ =ᶠ[𝓝 s]
      (fun z : ℂ =>
        (∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-z)) -
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-z) +
          z * ∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-z - 1)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    rw [LFunction_eq_partialSum_add_tail hχ hN hz, hIoi_eq z]
  rw [hEv.deriv_eq, hd_tot.deriv, ← hIoi_eq s, hIoi_log_eq]
  ring

/-- Generic right-half-plane bound `‖LFunction χ s‖ ≤ B * (s.re + |s.im|) / s.re`
for any non-principal `χ ≠ 1` whose step sum satisfies `‖stepSum χ t‖ ≤ B` on `t ≥ 1`. -/
theorem norm_LFunction_le_of_stepSum_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {B : ℝ} (_hB : 0 ≤ B)
    (hstep : ∀ t : ℝ, 1 ≤ t → ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t‖ ≤ B)
    {s : ℂ} (hs : 0 < s.re) :
    ‖LFunction χ s‖ ≤ B * (s.re + |s.im|) / s.re := by
  rw [LFunction_eq_mul_mellin_of_ne_one hχ hs, norm_mul]
  have hint_norm :
      ‖∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
        B / s.re := by
    have hdom : IntegrableOn (fun t : ℝ => B * t ^ (-s.re - 1)) (Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul B
    have hle :
        ‖∫ t in Ioi (1 : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
        ∫ t in Ioi (1 : ℝ), B * t ^ (-s.re - 1) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hdom ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := zero_lt_one.trans ht
      dsimp only
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      have hre : (-s - 1).re = -s.re - 1 := by simp
      rw [hre]
      exact mul_le_mul_of_nonneg_right (hstep t ht.le) (Real.rpow_nonneg ht0.le _)
    have heval : ∫ t in Ioi (1 : ℝ), B * t ^ (-s.re - 1) = B / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
      have hden : -s.re - 1 + 1 = -s.re := by ring
      rw [hden]; field_simp [hs.ne']
    exact hle.trans_eq heval
  have hns : ‖s‖ ≤ s.re + |s.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rwa [abs_of_pos hs] at h
  calc ‖s‖ *
        ‖∫ t in Ioi (1 : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖
      ≤ (s.re + |s.im|) * (B / s.re) :=
        mul_le_mul hns hint_norm (norm_nonneg _) (by linarith [abs_nonneg s.im])
    _ = B * (s.re + |s.im|) / s.re := by ring

/-- **Unconditional Pólya–Vinogradov Half-Plane Bound on `DirichletCharacter.LFunction`**:
for every primitive `χ ≠ 1` mod `q` and every `s : ℂ` with `0 < s.re`:
`‖LFunction χ s‖ ≤ (√q * (log q + 2)) * (s.re + |s.im|) / s.re`. -/
theorem norm_LFunction_le_polya_vinogradov {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖LFunction χ s‖ ≤
      (Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2)) * (s.re + |s.im|) / s.re :=
  norm_LFunction_le_of_stepSum_bound hχ
    (mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.log_natCast_nonneg q]))
    (fun t _ => polya_vinogradov_stepSum hprim hχ t) hs

/-- **Unconditional Pólya–Vinogradov Vertical-Strip Bound (`0 < σ ≤ 2`)**:
for every primitive `χ ≠ 1` mod `q`, `0 < σ ≤ 2`, and `t : ℝ`:
`‖LFunction χ (σ + I * t)‖ ≤ (√q * (log q + 2)) * (|t| + 2) / σ`. -/
theorem norm_LFunction_strip_le_polya_vinogradov {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {σ : ℝ} (hσ0 : 0 < σ) (hσ2 : σ ≤ 2) (t : ℝ) :
    ‖LFunction χ ((σ : ℂ) + I * (t : ℂ))‖ ≤
      (Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2)) * (|t| + 2) / σ := by
  have hs : 0 < ((σ : ℂ) + I * (t : ℂ)).re := by simpa using hσ0
  have h1 := norm_LFunction_le_polya_vinogradov hprim hχ hs
  have hre : ((σ : ℂ) + I * (t : ℂ)).re = σ := by simp
  have him : ((σ : ℂ) + I * (t : ℂ)).im = t := by simp
  rw [hre, him] at h1
  refine h1.trans ?_
  have hB : 0 ≤ Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.log_natCast_nonneg q])
  apply div_le_div_of_nonneg_right _ hσ0.le
  exact mul_le_mul_of_nonneg_left (by linarith) hB

/-- Helper: `Real.log 4 > 1.38` (and in particular `Real.log (q * (|t| + 2)) ≥ 1.38 > 1` for `q ≥ 2`). -/
private lemma log_four_gt : (1.38 : ℝ) < Real.log 4 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_gt_d9]

private lemma log_q_mul_abs_add_two_ge {q : ℕ} (hq : 2 ≤ q) (t : ℝ) :
    (1.38 : ℝ) < Real.log ((q : ℝ) * (|t| + 2)) := by
  have h4le : (4 : ℝ) ≤ (q : ℝ) * (|t| + 2) := by
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have htR : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    nlinarith
  exact lt_of_lt_of_le log_four_gt (Real.log_le_log (by norm_num) h4le)

private lemma exp_two_lt_eight : Real.exp 2 < 8 := by
  have h1 : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  rw [h2]
  nlinarith [Real.exp_pos 1]

/-- **Sharp Logarithmic Bound on `DirichletCharacter.LFunction χ` on `1 ≤ Re(s) ≤ 2`**:
for EVERY non-principal `χ ≠ 1` mod `q` (primitive or imprimitive!) and every `s : ℂ`
with `1 ≤ s.re ≤ 2`,
`‖LFunction χ s‖ ≤ 5 * Real.log (q * (|s.im| + 2))`. -/
theorem norm_LFunction_le_log_of_one_le_re {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs1 : 1 ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖LFunction χ s‖ ≤ 5 * Real.log ((q : ℝ) * (|s.im| + 2)) := by
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
  have hs0 : 0 < s.re := by linarith
  set L : ℝ := Real.log ((q : ℝ) * (|s.im| + 2))
  have hL : (1.38 : ℝ) < L := log_q_mul_abs_add_two_ge hq2 s.im
  set X : ℝ := (q : ℝ) * (|s.im| + 2)
  have hX4 : (4 : ℝ) ≤ X := by
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    nlinarith [abs_nonneg s.im]
  set N : ℕ := ⌊X⌋₊ + 1
  have hN1 : 1 ≤ N := Nat.succ_le_succ (Nat.zero_le _)
  have hN_ge : X ≤ (N : ℝ) := by
    dsimp only [N]; push_cast; exact (Nat.lt_floor_add_one X).le
  have hN_le : (N : ℝ) ≤ 2 * X := by
    dsimp only [N]; push_cast
    have hfl : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
    linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN1
  rw [LFunction_eq_partialSum_add_tail hχ hN1 hs0]
  -- Term 1: finite partial sum `≤ log N + 1`
  have hT1 : ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖ ≤ Real.log (N : ℝ) + 1 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Finset.Icc 1 N, ‖χ (n : ZMod q) * (n : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hn1R : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn1
          rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn1, neg_re]
          calc ‖χ (n : ZMod q)‖ * (n : ℝ) ^ (-s.re)
              ≤ 1 * (n : ℝ) ^ (-s.re) :=
                mul_le_mul_of_nonneg_right (χ.norm_le_one _) (Real.rpow_nonneg (by positivity) _)
            _ = (n : ℝ) ^ (-s.re) := one_mul _
            _ ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
            _ = ((n : ℝ))⁻¹ := Real.rpow_neg_one _
      _ ≤ Real.log (N : ℝ) + 1 := harmonic_sum_le_log_add_one hN1
  -- Term 2: boundary term `≤ q / N ≤ 1`
  have hT2 : ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN1, neg_re]
    have hpow : (N : ℝ) ^ (-s.re) ≤ ((N : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one (N : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hN1) (by linarith)
    calc ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ)‖ * (N : ℝ) ^ (-s.re)
        ≤ (q : ℝ) * ((N : ℝ))⁻¹ :=
          mul_le_mul (norm_stepSum_dirichletChar_le_modulus hχ (N : ℝ)) hpow
            (Real.rpow_nonneg hN_pos.le _) hq_pos.le
      _ = (q : ℝ) / (N : ℝ) := by rw [div_eq_mul_inv]
      _ ≤ 1 := by
          rw [div_le_one hN_pos]
          have : (q : ℝ) ≤ X := by dsimp only [X]; nlinarith [abs_nonneg s.im]
          linarith
  -- Term 3: tail integral `≤ 1`
  have hT3 : ‖s * ∫ t in Ioi (N : ℝ),
      Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤ 1 := by
    rw [norm_mul]
    have hdom : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-s.re - 1)) (Ioi (N : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hN_pos).const_mul (q : ℝ)
    have hint_le :
        ‖∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
        (q : ℝ) * (N : ℝ) ^ (-s.re) / s.re := by
      have h1 :
          ‖∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
          ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-s.re - 1) := by
        refine (norm_integral_le_integral_norm _).trans ?_
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hdom ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := hN_pos.trans ht
        dsimp only
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        have hre : (-s - 1).re = -s.re - 1 := by simp
        rw [hre]
        exact mul_le_mul_of_nonneg_right (norm_stepSum_dirichletChar_le_modulus hχ t)
          (Real.rpow_nonneg ht0.le _)
      have heval : ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-s.re - 1) = (q : ℝ) * (N : ℝ) ^ (-s.re) / s.re := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN_pos]
        have hden : -s.re - 1 + 1 = -s.re := by ring
        rw [hden]; field_simp [hs0.ne']
      exact h1.trans_eq heval
    have hns : ‖s‖ ≤ |s.im| + 2 := by
      have h := Complex.norm_le_abs_re_add_abs_im s
      rw [abs_of_pos hs0] at h
      linarith
    have hpow : (N : ℝ) ^ (-s.re) ≤ ((N : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one (N : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hN1) (by linarith)
    calc ‖s‖ *
          ‖∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖
        ≤ (|s.im| + 2) * ((q : ℝ) * (N : ℝ) ^ (-s.re) / s.re) :=
          mul_le_mul hns hint_le (norm_nonneg _) (by positivity)
      _ ≤ (|s.im| + 2) * ((q : ℝ) * ((N : ℝ))⁻¹ / 1) := by
          gcongr
      _ = X / (N : ℝ) := by dsimp only [X]; field_simp [hN_pos.ne']
      _ ≤ 1 := (div_le_one hN_pos).mpr hN_ge
  have hlogN : Real.log (N : ℝ) ≤ L + Real.log 2 := by
    have h1 := Real.log_le_log hN_pos hN_le
    rw [Real.log_mul (by norm_num) (by linarith : X ≠ 0)] at h1
    linarith
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  calc ‖(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)) -
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-s) +
          s * ∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)) -
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-s)‖ +
          ‖s * ∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ :=
        norm_add_le _ _
    _ ≤ (‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖ +
          ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-s)‖) +
          ‖s * ∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ (Real.log (N : ℝ) + 1 + 1) + 1 := by linarith
    _ ≤ 5 * L := by linarith

/-- **Sharp `log²` Derivative Bound on `DirichletCharacter.LFunction χ`** throughout the strip
`1 - 1 / log (q * (|s.im| + 2)) ≤ s.re ≤ 2` (in particular on `1 ≤ s.re ≤ 2`):
`‖deriv (LFunction χ) s‖ ≤ 288 * (Real.log (q * (|s.im| + 2))) ^ 2`. -/
theorem norm_deriv_LFunction_le_log_sq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ}
    (hs1 : 1 - (Real.log ((q : ℝ) * (|s.im| + 2)))⁻¹ ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖deriv (LFunction χ) s‖ ≤ 288 * (Real.log ((q : ℝ) * (|s.im| + 2))) ^ 2 := by
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
  set L : ℝ := Real.log ((q : ℝ) * (|s.im| + 2))
  have hL : (1.38 : ℝ) < L := log_q_mul_abs_add_two_ge hq2 s.im
  have hL_pos : 0 < L := by linarith
  have hL_ge1 : 1 ≤ L := by linarith
  have hinvL : L⁻¹ < 3 / 4 := by
    rw [inv_lt_comm₀ hL_pos (by norm_num : (0 : ℝ) < 3 / 4)]
    linarith
  have hs_quarter : (1 / 4 : ℝ) ≤ s.re := by linarith
  have hs0 : 0 < s.re := by linarith
  set X : ℝ := (q : ℝ) * (|s.im| + 2)
  have hX4 : (4 : ℝ) ≤ X := by
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    nlinarith [abs_nonneg s.im]
  set N : ℕ := ⌊X⌋₊ + 1
  have hN1 : 1 ≤ N := Nat.succ_le_succ (Nat.zero_le _)
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN1
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN1
  have hN_ge : X ≤ (N : ℝ) := by
    dsimp only [N]; push_cast; exact (Nat.lt_floor_add_one X).le
  have hN_le : (N : ℝ) ≤ 2 * X := by
    dsimp only [N]; push_cast
    have hfl : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
    linarith
  have hlogN_le : Real.log (N : ℝ) ≤ 2 * L := by
    have h1 := Real.log_le_log hN_pos hN_le
    rw [Real.log_mul (by norm_num) (by linarith : X ≠ 0)] at h1
    have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have hlogN_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1R
  -- Key factor `N ^ (1 - s.re) ≤ 8`
  have hN_pow : (N : ℝ) ^ (1 - s.re) ≤ 8 := by
    rw [Real.rpow_def_of_pos hN_pos]
    have hexp_le : Real.log (N : ℝ) * (1 - s.re) ≤ 2 := by
      rcases le_total 1 s.re with hge | hle
      · have hnp : Real.log (N : ℝ) * (1 - s.re) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hlogN_nn (by linarith)
        linarith
      · have h1s : 1 - s.re ≤ L⁻¹ := by linarith
        calc Real.log (N : ℝ) * (1 - s.re)
            ≤ (2 * L) * L⁻¹ := mul_le_mul hlogN_le h1s (by linarith) (by positivity)
          _ = 2 := by field_simp [hL_pos.ne']
    exact (Real.exp_le_exp.mpr hexp_le).trans exp_two_lt_eight.le
  -- Also for any `1 ≤ n ≤ N`, `n ^ (-s.re) ≤ 8 * n⁻¹`
  have hn_pow : ∀ n : ℕ, 1 ≤ n → n ≤ N → (n : ℝ) ^ (-s.re) ≤ 8 * ((n : ℝ))⁻¹ := by
    intro n hn1 hnN
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn1
    have hn0 : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1R
    have hsplit : (n : ℝ) ^ (-s.re) = (n : ℝ) ^ (1 - s.re) * ((n : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one (n : ℝ), ← Real.rpow_add hn0]; congr 1; ring
    rw [hsplit]
    have hfac : (n : ℝ) ^ (1 - s.re) ≤ 8 := by
      rcases le_total 1 s.re with hge | hle
      · exact (Real.rpow_le_one_of_one_le_of_nonpos hn1R (by linarith)).trans (by norm_num)
      · exact (Real.rpow_le_rpow hn0.le (by exact_mod_cast hnN) (by linarith)).trans hN_pow
    exact mul_le_mul_of_nonneg_right hfac (inv_nonneg.mpr hn0.le)
  -- Helper `N ^ (-s.re) = N ^ (1 - s.re) * N⁻¹`
  have hN_split : (N : ℝ) ^ (-s.re) = (N : ℝ) ^ (1 - s.re) * ((N : ℝ))⁻¹ := by
    rw [← Real.rpow_neg_one (N : ℝ), ← Real.rpow_add hN_pos]; congr 1; ring
  have hqN : (q : ℝ) * ((N : ℝ))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hN_pos]
    have : (q : ℝ) ≤ X := by dsimp only [X]; nlinarith [abs_nonneg s.im]
    linarith
  have hns : ‖s‖ ≤ |s.im| + 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hs0] at h; linarith
  have hsqN : ‖s‖ * (q : ℝ) * ((N : ℝ))⁻¹ ≤ 1 := by
    calc ‖s‖ * (q : ℝ) * ((N : ℝ))⁻¹
        ≤ (|s.im| + 2) * (q : ℝ) * ((N : ℝ))⁻¹ := by gcongr
      _ = X / (N : ℝ) := by dsimp only [X]; field_simp [hN_pos.ne']
      _ ≤ 1 := (div_le_one hN_pos).mpr hN_ge
  rw [deriv_LFunction_eq_partialSum_add_tail hχ hN1 hs0]
  -- Term 1: `≤ 48 * L^2`
  have hT1 : ‖-(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s))‖ ≤
      48 * L ^ 2 := by
    rw [norm_neg]
    have hsum_le :
        ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)‖ ≤
          8 * Real.log (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      have hn1R : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn1
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hn1R),
        Complex.norm_natCast_cpow_of_pos hn1, neg_re]
      have hlog_n : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (zero_lt_one.trans_le hn1R) (by exact_mod_cast hnN)
      calc ‖χ (n : ZMod q)‖ * Real.log (n : ℝ) * (n : ℝ) ^ (-s.re)
          ≤ 1 * Real.log (N : ℝ) * (8 * ((n : ℝ))⁻¹) := by
            refine mul_le_mul ?_ (hn_pow n hn1 hnN) (Real.rpow_nonneg (by positivity) _) (by positivity)
            exact mul_le_mul (χ.norm_le_one _) hlog_n (Real.log_nonneg hn1R) zero_le_one
        _ = 8 * Real.log (N : ℝ) * ((n : ℝ))⁻¹ := by ring
    have hharm := harmonic_sum_le_log_add_one hN1
    have h1 : Real.log (N : ℝ) + 1 ≤ 3 * L := by linarith
    calc ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)‖
        ≤ 8 * Real.log (N : ℝ) * (Real.log (N : ℝ) + 1) :=
          hsum_le.trans (mul_le_mul_of_nonneg_left hharm (by positivity))
      _ ≤ 8 * (2 * L) * (3 * L) := by
          refine mul_le_mul (by linarith) h1 (by positivity) (by positivity)
      _ = 48 * L ^ 2 := by ring
  -- Term 2: `≤ 16 * L^2`
  have hT2 : ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
      (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s)‖ ≤ 16 * L ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlogN_nn,
      Complex.norm_natCast_cpow_of_pos hN1, neg_re, hN_split]
    calc ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ)‖ *
          Real.log (N : ℝ) * ((N : ℝ) ^ (1 - s.re) * ((N : ℝ))⁻¹)
        ≤ (q : ℝ) * (2 * L) * (8 * ((N : ℝ))⁻¹) := by
          refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
          · exact mul_le_mul (norm_stepSum_dirichletChar_le_modulus hχ (N : ℝ)) hlogN_le
              hlogN_nn hq_pos.le
          · exact mul_le_mul_of_nonneg_right hN_pow (inv_nonneg.mpr hN_pos.le)
      _ = 16 * L * ((q : ℝ) * ((N : ℝ))⁻¹) := by ring
      _ ≤ 16 * L * 1 := mul_le_mul_of_nonneg_left hqN (by positivity)
      _ = 16 * L := mul_one _
      _ ≤ 16 * L ^ 2 := by nlinarith
  -- Term 3: `≤ 32 * L^2`
  have hT3 : ‖∫ t in Ioi (N : ℝ),
      Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
      32 * L ^ 2 := by
    have hdom : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-s.re - 1)) (Ioi (N : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hN_pos).const_mul (q : ℝ)
    have h1 :
        ‖∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
        (q : ℝ) * (N : ℝ) ^ (-s.re) / s.re := by
      have hle :
          ‖∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
          ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-s.re - 1) := by
        refine (norm_integral_le_integral_norm _).trans ?_
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hdom ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := hN_pos.trans ht
        dsimp only
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        have hre : (-s - 1).re = -s.re - 1 := by simp
        rw [hre]
        exact mul_le_mul_of_nonneg_right (norm_stepSum_dirichletChar_le_modulus hχ t)
          (Real.rpow_nonneg ht0.le _)
      have heval : ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-s.re - 1) = (q : ℝ) * (N : ℝ) ^ (-s.re) / s.re := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN_pos]
        have hden : -s.re - 1 + 1 = -s.re := by ring
        rw [hden]; field_simp [hs0.ne']
      exact hle.trans_eq heval
    refine h1.trans ?_
    rw [hN_split]
    have h4 : (s.re)⁻¹ ≤ 4 := by
      rw [inv_le_comm₀ hs0 (by norm_num : (0 : ℝ) < 4)]; linarith
    calc (q : ℝ) * ((N : ℝ) ^ (1 - s.re) * ((N : ℝ))⁻¹) / s.re
        = ((q : ℝ) * ((N : ℝ))⁻¹) * (N : ℝ) ^ (1 - s.re) * (s.re)⁻¹ := by ring
      _ ≤ 1 * 8 * 4 := by
          refine mul_le_mul ?_ h4 (inv_nonneg.mpr hs0.le) (by norm_num)
          exact mul_le_mul hqN hN_pow (Real.rpow_nonneg hN_pos.le _) zero_le_one
      _ = 32 := by norm_num
      _ ≤ 32 * L ^ 2 := by nlinarith
  -- Term 4: `≤ 192 * L^2`
  have hT4 : ‖s * ∫ t in Ioi (N : ℝ),
      Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
        (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤ 192 * L ^ 2 := by
    rw [norm_mul]
    have hint_log : IntegrableOn (fun t : ℝ => (q : ℝ) * (Real.log t * t ^ (-s.re - 1))) (Ioi (N : ℝ)) := by
      have hdom_int : IntegrableOn (fun t : ℝ => (s.re / 2)⁻¹ * t ^ (-1 - s.re / 2)) (Ioi (N : ℝ)) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - s.re / 2 < -1) hN_pos).const_mul _
      refine (hdom_int.mono' ?_ ?_).const_mul (q : ℝ)
      · exact (Real.measurable_log.mul (measurable_id.pow_const (-s.re - 1))).aestronglyMeasurable
      · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have ht1 : 1 ≤ t := hN1R.trans ht.le
        have ht0 : 0 < t := zero_lt_one.trans_le ht1
        have hlog_le : Real.log t ≤ t ^ (s.re / 2) / (s.re / 2) :=
          Real.log_le_rpow_div ht0.le (half_pos hs0)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.log_nonneg ht1) (Real.rpow_nonneg ht0.le _))]
        have hpow_comb : t ^ (s.re / 2) * t ^ (-s.re - 1) = t ^ (-1 - s.re / 2) := by
          rw [← Real.rpow_add ht0]; congr 1; ring
        calc Real.log t * t ^ (-s.re - 1)
            ≤ (t ^ (s.re / 2) / (s.re / 2)) * t ^ (-s.re - 1) :=
              mul_le_mul_of_nonneg_right hlog_le (Real.rpow_nonneg ht0.le _)
          _ = (s.re / 2)⁻¹ * (t ^ (s.re / 2) * t ^ (-s.re - 1)) := by ring
          _ = (s.re / 2)⁻¹ * t ^ (-1 - s.re / 2) := by rw [hpow_comb]
    have h1 :
        ‖∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
            (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤
        (q : ℝ) * (((s.re * Real.log (N : ℝ) + 1) / s.re ^ 2) * (N : ℝ) ^ (-s.re)) := by
      have hle :
          ‖∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
              (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤
          ∫ t in Ioi (N : ℝ), (q : ℝ) * (Real.log t * t ^ (-s.re - 1)) := by
        refine (norm_integral_le_integral_norm _).trans ?_
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hint_log ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have ht1 : 1 ≤ t := hN1R.trans ht.le
        have ht0 : 0 < t := zero_lt_one.trans_le ht1
        dsimp only
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg ht1),
          Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        have hre : (-s - 1).re = -s.re - 1 := by simp
        rw [hre, mul_assoc]
        exact mul_le_mul_of_nonneg_right (norm_stepSum_dirichletChar_le_modulus hχ t)
          (mul_nonneg (Real.log_nonneg ht1) (Real.rpow_nonneg ht0.le _))
      rw [integral_const_mul, integral_Ioi_log_mul_rpow hN1R hs0] at hle
      exact hle
    have hfrac : (s.re * Real.log (N : ℝ) + 1) / s.re ^ 2 ≤ 24 * L := by
      have h4 : (s.re)⁻¹ ≤ 4 := by
        rw [inv_le_comm₀ hs0 (by norm_num : (0 : ℝ) < 4)]; linarith
      have h16 : (s.re ^ 2)⁻¹ ≤ 16 := by
        have : (s.re ^ 2)⁻¹ = (s.re)⁻¹ ^ 2 := by rw [inv_pow]
        rw [this]; nlinarith [inv_nonneg.mpr hs0.le]
      have hsplit2 : (s.re * Real.log (N : ℝ) + 1) / s.re ^ 2 =
          Real.log (N : ℝ) * (s.re)⁻¹ + (s.re ^ 2)⁻¹ := by
        field_simp [hs0.ne']
      rw [hsplit2]
      have hm1 : Real.log (N : ℝ) * (s.re)⁻¹ ≤ (2 * L) * 4 :=
        mul_le_mul hlogN_le h4 (inv_nonneg.mpr hs0.le) (by positivity)
      linarith
    calc ‖s‖ *
          ‖∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
              (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)‖
        ≤ ‖s‖ * ((q : ℝ) * (((s.re * Real.log (N : ℝ) + 1) / s.re ^ 2) * (N : ℝ) ^ (-s.re))) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg s)
      _ = (‖s‖ * (q : ℝ) * ((N : ℝ))⁻¹) * (N : ℝ) ^ (1 - s.re) *
            ((s.re * Real.log (N : ℝ) + 1) / s.re ^ 2) := by
          rw [hN_split]; ring
      _ ≤ 1 * 8 * (24 * L) := by
          refine mul_le_mul ?_ hfrac (by positivity) (by norm_num)
          exact mul_le_mul hsqN hN_pow (Real.rpow_nonneg hN_pos.le _) zero_le_one
      _ = 192 * L := by ring
      _ ≤ 192 * L ^ 2 := by nlinarith
  -- Combine all 4 terms
  calc ‖-(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) +
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
            (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s) +
          (∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)) -
          s * ∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
              (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)‖
      ≤ ‖-(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) +
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
              (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s) +
            (∫ t in Ioi (N : ℝ),
              Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1))‖ +
          ‖s * ∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
              (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)‖ := norm_sub_le _ _
    _ ≤ (‖-(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s))‖ +
          ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
            (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s)‖) +
          ‖∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ +
          ‖s * ∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
              (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)‖ := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 48 * L ^ 2 + 16 * L ^ 2 + 32 * L ^ 2 + 192 * L ^ 2 := by linarith
    _ = 288 * L ^ 2 := by ring

/-- Specialization of `norm_deriv_LFunction_le_log_sq` to `1 ≤ s.re ≤ 2`. -/
theorem norm_deriv_LFunction_le_log_sq_of_one_le_re {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ} (hs1 : 1 ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖deriv (LFunction χ) s‖ ≤ 288 * (Real.log ((q : ℝ) * (|s.im| + 2))) ^ 2 := by
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
  have hL : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) := by
    linarith [log_q_mul_abs_add_two_ge hq2 s.im]
  exact norm_deriv_LFunction_le_log_sq hχ (by linarith [inv_pos.mpr hL]) hs2

/-! ### Principal Character Bounds & Right-of-1 Logarithmic Derivative Bounds -/

/-- Elementary telescoping bound `∑_{n=1}^M n^{-(1 + x)} ≤ 1 + (1 - M^{-x}) / x` for `x > 0`, `M ≥ 1`. -/
private lemma sum_rpow_neg_one_add_le {x : ℝ} (hx : 0 < x) {M : ℕ} (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-(1 + x)) ≤ 1 + (1 - (M : ℝ) ^ (-x)) / x := by
  induction M, hM using Nat.le_induction with
  | base =>
    simp
  | succ k hk ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : k + 1 ∉ Finset.Icc 1 k := by simp
    rw [hIcc, Finset.sum_insert hnot]
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    have hk_lt : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hdiff : x * ((k + 1 : ℕ) : ℝ) ^ (-(1 + x)) ≤
        (k : ℝ) ^ (-x) - ((k + 1 : ℕ) : ℝ) ^ (-x) := by
      have hcont : ContinuousOn (fun u : ℝ => -(u ^ (-x))) (Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ)) := by
        refine ContinuousOn.neg (ContinuousOn.rpow_const continuousOn_id fun u hu => ?_)
        exact Or.inl (lt_of_lt_of_le hk_pos hu.1).ne'
      have hderiv : ∀ u ∈ Set.Ioo (k : ℝ) ((k + 1 : ℕ) : ℝ),
          HasDerivAt (fun t : ℝ => -(t ^ (-x))) (x * u ^ (-x - 1)) u := by
        intro u hu
        have hu0 : 0 < u := hk_pos.trans hu.1
        have h := (Real.hasDerivAt_rpow_const (p := -x) (Or.inl hu0.ne')).neg
        refine h.congr_deriv ?_; ring
      obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun u : ℝ => -(u ^ (-x)))
        (fun u => x * u ^ (-x - 1)) hk_lt hcont hderiv
      have hden : ((k + 1 : ℕ) : ℝ) - (k : ℝ) = 1 := by push_cast; ring
      rw [hden, div_one] at hslope
      have hsub : -((k + 1 : ℕ) : ℝ) ^ (-x) - -((k : ℝ) ^ (-x)) =
          (k : ℝ) ^ (-x) - ((k + 1 : ℕ) : ℝ) ^ (-x) := by ring
      rw [hsub] at hslope
      rw [← hslope]
      have hc0 : 0 < c := hk_pos.trans hc.1
      have hmono : ((k + 1 : ℕ) : ℝ) ^ (-(1 + x)) ≤ c ^ (-x - 1) := by
        rw [show -(1 + x) = -x - 1 by ring]
        exact Real.rpow_le_rpow_of_nonpos hc0 hc.2.le (by linarith)
      exact mul_le_mul_of_nonneg_left hmono hx.le
    have hstep : ((k + 1 : ℕ) : ℝ) ^ (-(1 + x)) ≤
        ((k : ℝ) ^ (-x) - ((k + 1 : ℕ) : ℝ) ^ (-x)) / x := by
      rw [le_div_iff₀ hx]; linarith
    have halg : (1 + (1 - (k : ℝ) ^ (-x)) / x) +
        ((k : ℝ) ^ (-x) - ((k + 1 : ℕ) : ℝ) ^ (-x)) / x =
        1 + (1 - ((k + 1 : ℕ) : ℝ) ^ (-x)) / x := by
      field_simp [hx.ne']; ring
    linarith

/-- Upper bound `‖LFunction (1_q) (1 + x)‖ ≤ 1 + 1 / x` for every `q ≥ 1` and `x > 0`. -/
theorem norm_LFunction_one_real_le {q : ℕ} [NeZero q] {x : ℝ} (hx : 0 < x) :
    ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ≤ 1 + 1 / x := by
  have hs : 1 < (1 + (x : ℂ)).re := by simp [hx]
  rw [DirichletCharacter.LFunction_eq_LSeries (1 : DirichletCharacter ℂ q) hs]
  have hsum : LSeriesSummable (fun n => (1 : DirichletCharacter ℂ q) (n : ZMod q)) (1 + (x : ℂ)) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re _ hs
  have hsum_real : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-(1 + x))) := by
    have h1 := Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 1 + x)
    refine h1.congr fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp [Real.zero_rpow (by linarith : 1 + x ≠ 0)]
    · simp only [hn, ↓reduceIte, Real.rpow_neg (Nat.cast_nonneg n)]
  have htsum_le : ∑' n : ℕ, (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-(1 + x))) ≤ 1 + 1 / x := by
    refine hsum_real.tsum_le_of_sum_range_le (fun N => ?_)
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp; positivity
    · have hsplit : Finset.range N = insert 0 (Finset.Icc 1 (N - 1)) := by
        ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hsplit, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 (N - 1))]
      simp only [↓reduceIte, zero_add]
      have hcongr : ∑ n ∈ Finset.Icc 1 (N - 1), (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-(1 + x))) =
          ∑ n ∈ Finset.Icc 1 (N - 1), (n : ℝ) ^ (-(1 + x)) :=
        Finset.sum_congr rfl fun n hn => by
          have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
          simp [hn0]
      rw [hcongr]
      rcases Nat.eq_zero_or_pos (N - 1) with h0 | hpos
      · rw [h0]; simp; positivity
      · have hbd := sum_rpow_neg_one_add_le hx hpos
        have hnn : 0 ≤ (((N - 1 : ℕ) : ℝ)) ^ (-x) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hdiv : (1 - (((N - 1 : ℕ) : ℝ)) ^ (-x)) / x ≤ 1 / x :=
          div_le_div_of_nonneg_right (by linarith) hx.le
        linarith
  have hnorm_le :
      ‖LSeries (fun n => (1 : DirichletCharacter ℂ q) (n : ZMod q)) (1 + (x : ℂ))‖ ≤
        ∑' n : ℕ, (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-(1 + x))) := by
    unfold LSeries
    refine (norm_tsum_le_tsum_norm hsum.norm).trans ?_
    refine hsum.norm.tsum_le_tsum (fun n => ?_) hsum_real
    by_cases hn : n = 0
    · subst hn; simp [LSeries.term_zero]
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      simp only [hn, ↓reduceIte]
      rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_natCast_cpow_of_pos hn_pos]
      have hre : (1 + (x : ℂ)).re = 1 + x := by simp
      rw [hre, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
      simpa using mul_le_mul_of_nonneg_right ((1 : DirichletCharacter ℂ q).norm_le_one (n : ZMod q))
        (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  exact hnorm_le.trans htsum_le

theorem norm_LFunction_one_real_le_two_div {q : ℕ} [NeZero q] {x : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ≤ 2 / x := by
  have h1 := norm_LFunction_one_real_le (q := q) hx0
  have h2 : (1 : ℝ) ≤ 1 / x := (one_le_div hx0).mpr hx1
  linarith [show 1 / x + 1 / x = 2 / x by ring]

/-- Period count of integers coprime to `q` in any block of length `q` equals `φ(q)`. -/
private lemma sum_coprime_Ico_period {q : ℕ} [NeZero q] (M : ℕ) :
    ∑ n ∈ Finset.Ico M (M + q), (if Nat.Coprime n q then (1 : ℝ) else 0) = (q.totient : ℝ) := by
  have hbij :
      ∑ n ∈ Finset.Ico M (M + q), (if Nat.Coprime n q then (1 : ℝ) else 0) =
        ∑ a : ZMod q, (if IsUnit a then (1 : ℝ) else 0) := by
    have hshift :
        ∑ n ∈ Finset.Ico M (M + q), (if Nat.Coprime n q then (1 : ℝ) else 0) =
          ∑ k ∈ Finset.range q, (if IsUnit ((M + k : ℕ) : ZMod q) then (1 : ℝ) else 0) := by
      refine Finset.sum_bij (fun n _ => n - M) ?_ ?_ ?_ ?_
      · intro n hn; simp only [Finset.mem_Ico] at hn; exact Finset.mem_range.mpr (by omega)
      · intro n₁ hn₁ n₂ hn₂ h; simp only [Finset.mem_Ico] at hn₁ hn₂; omega
      · intro k hk; simp only [Finset.mem_range] at hk
        exact ⟨M + k, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro n hn; simp only [Finset.mem_Ico] at hn
        have hsub : M + (n - M) = n := by omega
        rw [hsub]
        simp [ZMod.isUnit_iff_coprime]
    rw [hshift]
    have hrange :
        ∑ k ∈ Finset.range q, (if IsUnit ((M + k : ℕ) : ZMod q) then (1 : ℝ) else 0) =
          ∑ a : ZMod q, (if IsUnit ((M : ZMod q) + a) then (1 : ℝ) else 0) := by
      refine Finset.sum_bij (fun k _ => (k : ZMod q)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro k₁ hk₁ k₂ hk₂ h
        simp only [Finset.mem_range] at hk₁ hk₂
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hk₁, Nat.mod_eq_of_lt hk₂] at hv
        exact hv
      · intro a _
        exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
      · intro k _; simp [Nat.cast_add]
    rw [hrange]
    exact Fintype.sum_equiv (Equiv.addLeft (M : ZMod q)) _ _ fun _ => rfl
  rw [hbij]
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (Finset.univ.filter (fun a : ZMod q => IsUnit a)).card = Fintype.card (ZMod q)ˣ := by
    refine Finset.card_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q)) ?_ ?_ ?_ |>.symm
    · intro u _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.isUnit⟩
    · intro u₁ _ u₂ _ h; exact Units.ext h
    · intro a ha
      obtain ⟨u, rfl⟩ := (Finset.mem_filter.mp ha).2
      exact ⟨u, Finset.mem_univ _, rfl⟩
  rw [hcard, ZMod.card_units_eq_totient]

/-- Periodic remainder bound for the principal character step sum:
`‖stepSum (1_q) u - (φ(q) / q) * u‖ ≤ q` for all `u ≥ 0`. -/
theorem norm_stepSum_principal_sub_linear_le {q : ℕ} [NeZero q] {u : ℝ} (hu : 0 ≤ u) :
    ‖Stage3RealAnalyticLandau.stepSum (fun n => (1 : DirichletCharacter ℂ q) (n : ZMod q)) u -
      ((((q.totient : ℝ) / (q : ℝ)) * u : ℝ) : ℂ)‖ ≤ (q : ℝ) := by
  have hq_pos : 0 < q := NeZero.pos q
  have hq_posR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_pos
  have hreal :
      Stage3RealAnalyticLandau.stepSum (fun n => (1 : DirichletCharacter ℂ q) (n : ZMod q)) u =
        ((∑ n ∈ Finset.Icc 1 ⌊u⌋₊, if Nat.Coprime n q then (1 : ℝ) else 0 : ℝ) : ℂ) := by
    unfold Stage3RealAnalyticLandau.stepSum
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only
    rw [Stage2DirichletAP.principal_char_apply_nat]
    split_ifs <;> simp
  rw [hreal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  set N := ⌊u⌋₊
  set m := N / q
  set r := N % q
  have hN : N = q * m + r := (Nat.div_add_mod N q).symm
  have hr : r < q := Nat.mod_lt N hq_pos
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (1 + q * m) ∪ Finset.Ico (1 + q * m) (1 + N) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.Ico 1 (1 + q * m)) (Finset.Ico (1 + q * m) (1 + N)) := by
    rw [Finset.disjoint_left]
    intro n h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
  have hblocks : ∀ j : ℕ,
      ∑ n ∈ Finset.Ico 1 (1 + q * j), (if Nat.Coprime n q then (1 : ℝ) else 0) =
        (j : ℝ) * (q.totient : ℝ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hqj : q * (j + 1) = q * j + q := by ring
      have hsp : Finset.Ico 1 (1 + q * (j + 1)) =
          Finset.Ico 1 (1 + q * j) ∪ Finset.Ico (1 + q * j) (1 + q * j + q) := by
        ext n; simp only [Finset.mem_Ico, Finset.mem_union]; omega
      have hd : Disjoint (Finset.Ico 1 (1 + q * j)) (Finset.Ico (1 + q * j) (1 + q * j + q)) := by
        rw [Finset.disjoint_left]
        intro n h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
      rw [hsp, Finset.sum_union hd, ih, sum_coprime_Ico_period (1 + q * j)]
      push_cast; ring
  rw [hIcc, Finset.sum_union hdisj, hblocks m]
  set R : ℝ := ∑ n ∈ Finset.Ico (1 + q * m) (1 + N), if Nat.Coprime n q then (1 : ℝ) else 0
  have hR_nn : 0 ≤ R := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hR_le : R ≤ (q : ℝ) := by
    calc R ≤ ∑ _n ∈ Finset.Ico (1 + q * m) (1 + N), (1 : ℝ) :=
            Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num
      _ = ((Finset.Ico (1 + q * m) (1 + N)).card : ℝ) := by simp
      _ = (r : ℝ) := by rw [Nat.card_Ico]; exact_mod_cast (by omega : 1 + N - (1 + q * m) = r)
      _ ≤ (q : ℝ) := by exact_mod_cast hr.le
  set μ : ℝ := (q.totient : ℝ) / (q : ℝ)
  have hμ_nn : 0 ≤ μ := div_nonneg (Nat.cast_nonneg _) hq_posR.le
  have hμ_le1 : μ ≤ 1 := (div_le_one hq_posR).mpr (by exact_mod_cast Nat.totient_le q)
  have hu_ge : ((q * m : ℕ) : ℝ) ≤ u := by
    have h1 : (q * m : ℕ) ≤ N := by omega
    exact le_trans (by exact_mod_cast h1) (Nat.floor_le hu)
  have hu_lt : u - ((q * m : ℕ) : ℝ) ≤ (q : ℝ) := by
    have h1 : u < (N : ℝ) + 1 := Nat.lt_floor_add_one u
    have h2 : (N : ℝ) = ((q * m : ℕ) : ℝ) + (r : ℝ) := by exact_mod_cast hN
    have hr1 : (r : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hr
    linarith
  have hlin_split : μ * u = (m : ℝ) * (q.totient : ℝ) + μ * (u - ((q * m : ℕ) : ℝ)) := by
    dsimp only [μ]; push_cast; field_simp [hq_posR.ne']; ring
  have htail_nn : 0 ≤ μ * (u - ((q * m : ℕ) : ℝ)) := mul_nonneg hμ_nn (by linarith)
  have htail_le : μ * (u - ((q * m : ℕ) : ℝ)) ≤ (q : ℝ) := by
    calc μ * (u - ((q * m : ℕ) : ℝ)) ≤ 1 * (q : ℝ) :=
          mul_le_mul hμ_le1 hu_lt (by linarith) zero_le_one
      _ = (q : ℝ) := one_mul _
  rw [hlin_split]
  have hcancel : (m : ℝ) * (q.totient : ℝ) + R -
      ((m : ℝ) * (q.totient : ℝ) + μ * (u - ((q * m : ℕ) : ℝ))) =
      R - μ * (u - ((q * m : ℕ) : ℝ)) := by ring
  rw [hcancel, abs_le]
  constructor <;> linarith

/-- **Sharp Logarithmic Bound for the Principal Character `LFunction (1_q)` off the Real Axis**:
for every `q ≥ 2` (`[NeZero q]`), `0 < x ≤ 1`, and `1 ≤ |y|`,
`‖LFunction (1_q) ((1 + x) + I * y)‖ ≤ 6 * Real.log (q * (|y| + 2))`. -/
theorem norm_LFunction_one_strip_le {q : ℕ} [NeZero q] (hq : 2 ≤ q) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy : 1 ≤ |y|) :
    ‖LFunction (1 : DirichletCharacter ℂ q) (((1 + x : ℝ) : ℂ) + I * (y : ℂ))‖ ≤
      6 * Real.log ((q : ℝ) * (|y| + 2)) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
  set s : ℂ := ((1 + x : ℝ) : ℂ) + I * (y : ℂ)
  have hs_re : s.re = 1 + x := by simp [s]
  have hs_im : s.im = y := by simp [s]
  have hs1 : 1 < s.re := by linarith
  have hs0 : 0 < s.re := by linarith
  have hs_ne1 : s - 1 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp [hs_re] at this; linarith
  set L : ℝ := Real.log ((q : ℝ) * (|y| + 2))
  have hL : (1.38 : ℝ) < L := log_q_mul_abs_add_two_ge hq y
  set X : ℝ := (q : ℝ) * (|y| + 2)
  have hX4 : (4 : ℝ) ≤ X := by
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith [abs_nonneg y]
  set N : ℕ := ⌊X⌋₊ + 1
  have hN1 : 1 ≤ N := Nat.succ_le_succ (Nat.zero_le _)
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN1
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN1
  have hN_ge : X ≤ (N : ℝ) := by
    dsimp only [N]; push_cast; exact (Nat.lt_floor_add_one X).le
  have hN_le : (N : ℝ) ≤ 2 * X := by
    dsimp only [N]; push_cast
    have hfl : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
    linarith
  set μ : ℝ := (q.totient : ℝ) / (q : ℝ)
  have hμ_nn : 0 ≤ μ := div_nonneg (Nat.cast_nonneg _) hq_pos.le
  have hμ_le1 : μ ≤ 1 := (div_le_one hq_pos).mpr (by exact_mod_cast Nat.totient_le q)
  set S : ℝ → ℂ := Stage3RealAnalyticLandau.stepSum (fun n => (1 : DirichletCharacter ℂ q) (n : ZMod q))
  set E : ℝ → ℂ := fun t => S t - ((μ * t : ℝ) : ℂ)
  have hS_bd : ∀ t : ℝ, 1 ≤ t → ‖S t‖ ≤ 1 * t ^ (1 : ℝ) := by
    intro t ht
    rw [one_mul, Real.rpow_one]
    have h1 : ‖S t‖ ≤ (⌊t⌋₊ : ℝ) := by
      dsimp only [S, Stage3RealAnalyticLandau.stepSum]
      calc ‖∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (1 : DirichletCharacter ℂ q) (n : ZMod q)‖
          ≤ ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ‖(1 : DirichletCharacter ℂ q) (n : ZMod q)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) :=
            Finset.sum_le_sum fun n _ => (1 : DirichletCharacter ℂ q).norm_le_one _
        _ = (⌊t⌋₊ : ℝ) := by simp
    exact h1.trans (Nat.floor_le (by linarith))
  have hE_bd : ∀ t : ℝ, 1 ≤ t → ‖E t‖ ≤ (q : ℝ) := fun t ht =>
    norm_stepSum_principal_sub_linear_le (by linarith)
  -- Exact Abelian summation split at `N`:
  -- `L(1_q, s) = ∑_{n=1}^N 1_q(n) n^{-s} - E(N) N^{-s} + μ N^{1-s}/(s-1) + s ∫_{Ioi N} E(t) t^{-s-1} dt`
  have hL_eq :
      LFunction (1 : DirichletCharacter ℂ q) s =
        (∑ n ∈ Finset.Icc 1 N, (1 : DirichletCharacter ℂ q) (n : ZMod q) * (n : ℂ) ^ (-s)) -
          E (N : ℝ) * (N : ℂ) ^ (-s) +
          (μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1) +
          s * ∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1) := by
    rw [DirichletCharacter.LFunction_eq_LSeries _ hs1]
    have hsum := DirichletCharacter.LSeriesSummable_of_one_lt_re (1 : DirichletCharacter ℂ q) hs1
    have hmel := Stage3RealAnalyticLandau.LSeries_eq_mul_mellin_stepSum hS_bd hs1 hsum
    have hintS : IntegrableOn (fun t : ℝ => S t * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) :=
      Stage3RealAnalyticLandau.integrableOn_mellin_of_rpow_bound
        (Stage3RealAnalyticLandau.measurable_stepSum _) hS_bd hs1
    rw [hmel, integral_Ioi_one_eq_interval_add_Ioi hN1R hintS, mul_add]
    have hab := Stage3RealAnalyticLandau.abel_summation_dirichlet
      (fun n => (1 : DirichletCharacter ℂ q) (n : ZMod q)) hN1R s
    rw [Nat.floor_natCast] at hab
    have hlin_int : IntegrableOn (fun t : ℝ => ((μ * t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) (Ioi (N : ℝ)) := by
      have ha_pow : (-s).re < -1 := by simp [hs_re]; linarith
      refine IntegrableOn.congr_fun ((integrableOn_Ioi_cpow_of_lt ha_pow hN_pos).const_mul (μ : ℂ))
        (fun t ht => ?_) measurableSet_Ioi
      have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (hN_pos.trans ht).ne'
      rw [Complex.ofReal_mul, mul_assoc, Complex.cpow_sub _ _ htC, Complex.cpow_one]
      field_simp
    have hlin_val :
        ∫ t in Ioi (N : ℝ), ((μ * t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) =
          (μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1) := by
      have ha_pow : (-s).re < -1 := by simp [hs_re]; linarith
      have hcongr : EqOn (fun t : ℝ => ((μ * t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))
          (fun t : ℝ => (μ : ℂ) * (t : ℂ) ^ (-s)) (Ioi (N : ℝ)) := fun t ht => by
        have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (hN_pos.trans ht).ne'
        dsimp only
        rw [Complex.ofReal_mul, mul_assoc, Complex.cpow_sub _ _ htC, Complex.cpow_one]
        field_simp
      rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
        integral_Ioi_cpow_of_lt ha_pow hN_pos]
      have h1s' : -s + 1 = 1 - s := by ring
      have h1s_ne : 1 - s ≠ 0 := by intro h; apply hs_ne1; linear_combination -h
      rw [Complex.ofReal_natCast, h1s']
      field_simp [hs_ne1, h1s_ne]
      ring
    have hE_int : IntegrableOn (fun t : ℝ => E t * (t : ℂ) ^ (-s - 1)) (Ioi (N : ℝ)) := by
      have h1 : IntegrableOn (fun t : ℝ => S t * (t : ℂ) ^ (-s - 1)) (Ioi (N : ℝ)) :=
        hintS.mono_set (Ioi_subset_Ioi hN1R)
      refine IntegrableOn.congr_fun (h1.sub hlin_int) (fun t _ => ?_) measurableSet_Ioi
      dsimp only [Pi.sub_apply, E]; ring
    have hsplit_int :
        ∫ t in Ioi (N : ℝ), S t * (t : ℂ) ^ (-s - 1) =
          (∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)) +
            (μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1) := by
      have hpt : EqOn (fun t : ℝ => S t * (t : ℂ) ^ (-s - 1))
          (fun t : ℝ => E t * (t : ℂ) ^ (-s - 1) + ((μ * t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))
          (Ioi (N : ℝ)) := fun t _ => by dsimp only [E]; ring
      rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add hE_int hlin_int, hlin_val]
    have hN_pow : (N : ℂ) ^ (1 - s) = (N : ℂ) * (N : ℂ) ^ (-s) := by
      have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN_pos.ne'
      rw [Complex.cpow_sub _ _ hNC, Complex.cpow_one, Complex.cpow_neg, div_eq_mul_inv]
    rw [hsplit_int]
    have hS_N : S (N : ℝ) = E (N : ℝ) + (μ : ℂ) * (N : ℂ) := by
      dsimp only [E]; push_cast; ring
    have hmul_comb :
        -((μ : ℂ) * (N : ℂ)) * (N : ℂ) ^ (-s) + s * ((μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1)) =
          (μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1) := by
      rw [hN_pow]
      field_simp [hs_ne1]
      ring
    calc (s * ∫ t in (1 : ℝ)..(N : ℝ), S t * (t : ℂ) ^ (-s - 1)) +
            s * ((∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)) +
              (μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1))
        = (∑ n ∈ Finset.Icc 1 N, (1 : DirichletCharacter ℂ q) (n : ZMod q) * (n : ℂ) ^ (-s)) -
            S (N : ℝ) * (N : ℂ) ^ (-s) +
            s * ((∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)) +
              (μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1)) := by
          linear_combination -hab
      _ = (∑ n ∈ Finset.Icc 1 N, (1 : DirichletCharacter ℂ q) (n : ZMod q) * (n : ℂ) ^ (-s)) -
            E (N : ℝ) * (N : ℂ) ^ (-s) +
            (-((μ : ℂ) * (N : ℂ)) * (N : ℂ) ^ (-s) + s * ((μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1))) +
            s * ∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1) := by
          rw [hS_N]; ring
      _ = (∑ n ∈ Finset.Icc 1 N, (1 : DirichletCharacter ℂ q) (n : ZMod q) * (n : ℂ) ^ (-s)) -
            E (N : ℝ) * (N : ℂ) ^ (-s) +
            (μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1) +
            s * ∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1) := by
          rw [hmul_comb]
  rw [hL_eq]
  -- Bound the 4 terms
  have hT1 : ‖∑ n ∈ Finset.Icc 1 N, (1 : DirichletCharacter ℂ q) (n : ZMod q) * (n : ℂ) ^ (-s)‖ ≤
      Real.log (N : ℝ) + 1 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Finset.Icc 1 N, ‖(1 : DirichletCharacter ℂ q) (n : ZMod q) * (n : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hn1R : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn1
          rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn1, neg_re, hs_re]
          calc ‖(1 : DirichletCharacter ℂ q) (n : ZMod q)‖ * (n : ℝ) ^ (-(1 + x))
              ≤ 1 * (n : ℝ) ^ (-(1 + x)) :=
                mul_le_mul_of_nonneg_right ((1 : DirichletCharacter ℂ q).norm_le_one _)
                  (Real.rpow_nonneg (by positivity) _)
            _ = (n : ℝ) ^ (-(1 + x)) := one_mul _
            _ ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
            _ = ((n : ℝ))⁻¹ := Real.rpow_neg_one _
      _ ≤ Real.log (N : ℝ) + 1 := harmonic_sum_le_log_add_one hN1
  have hT2 : ‖E (N : ℝ) * (N : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN1, neg_re, hs_re]
    have hpow : (N : ℝ) ^ (-(1 + x)) ≤ ((N : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one (N : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le hN1R (by linarith)
    calc ‖E (N : ℝ)‖ * (N : ℝ) ^ (-(1 + x))
        ≤ (q : ℝ) * ((N : ℝ))⁻¹ :=
          mul_le_mul (hE_bd (N : ℝ) hN1R) hpow (Real.rpow_nonneg hN_pos.le _) hq_pos.le
      _ = (q : ℝ) / (N : ℝ) := by rw [div_eq_mul_inv]
      _ ≤ 1 := by
          rw [div_le_one hN_pos]
          have : (q : ℝ) ≤ X := by dsimp only [X]; nlinarith [abs_nonneg y]
          linarith
  have hT3 : ‖(μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hμ_nn,
      Complex.norm_natCast_cpow_of_pos hN1]
    have hre1 : (1 - s).re = -x := by simp [hs_re]
    rw [hre1]
    have hpow1 : (N : ℝ) ^ (-x) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1R (by linarith)
    have hden : 1 ≤ ‖s - 1‖ := by
      have him1 : (s - 1).im = y := by simp [hs_im]
      calc (1 : ℝ) ≤ |y| := hy
        _ = |(s - 1).im| := by rw [him1]
        _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
    rw [div_le_one (by linarith)]
    calc μ * (N : ℝ) ^ (-x) ≤ 1 * 1 :=
          mul_le_mul hμ_le1 hpow1 (Real.rpow_nonneg hN_pos.le _) zero_le_one
      _ = 1 := one_mul _
      _ ≤ ‖s - 1‖ := hden
  have hT4 : ‖s * ∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)‖ ≤ 1 := by
    rw [norm_mul]
    have hdom : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-s.re - 1)) (Ioi (N : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hN_pos).const_mul (q : ℝ)
    have hint_le :
        ‖∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)‖ ≤ (q : ℝ) * (N : ℝ) ^ (-s.re) / s.re := by
      have h1 :
          ‖∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)‖ ≤
            ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-s.re - 1) := by
        refine (norm_integral_le_integral_norm _).trans ?_
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hdom ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have ht1 : 1 ≤ t := hN1R.trans ht.le
        have ht0 : 0 < t := zero_lt_one.trans_le ht1
        dsimp only
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        have hre : (-s - 1).re = -s.re - 1 := by simp
        rw [hre]
        exact mul_le_mul_of_nonneg_right (hE_bd t ht1) (Real.rpow_nonneg ht0.le _)
      have heval : ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-s.re - 1) = (q : ℝ) * (N : ℝ) ^ (-s.re) / s.re := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN_pos]
        have hden : -s.re - 1 + 1 = -s.re := by ring
        rw [hden]; field_simp [hs0.ne']
      exact h1.trans_eq heval
    have hns : ‖s‖ ≤ |y| + 2 := by
      have h := Complex.norm_le_abs_re_add_abs_im s
      rw [abs_of_pos hs0, hs_re, hs_im] at h; linarith
    have hpow : (N : ℝ) ^ (-s.re) ≤ ((N : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one (N : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le hN1R (by linarith)
    calc ‖s‖ * ‖∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)‖
        ≤ (|y| + 2) * ((q : ℝ) * (N : ℝ) ^ (-s.re) / s.re) :=
          mul_le_mul hns hint_le (norm_nonneg _) (by positivity)
      _ ≤ (|y| + 2) * ((q : ℝ) * ((N : ℝ))⁻¹ / 1) := by gcongr
      _ = X / (N : ℝ) := by dsimp only [X]; field_simp [hN_pos.ne']
      _ ≤ 1 := (div_le_one hN_pos).mpr hN_ge
  have hlogN : Real.log (N : ℝ) ≤ L + Real.log 2 := by
    have h1 := Real.log_le_log hN_pos hN_le
    rw [Real.log_mul (by norm_num) (by linarith : X ≠ 0)] at h1
    linarith
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  calc ‖(∑ n ∈ Finset.Icc 1 N, (1 : DirichletCharacter ℂ q) (n : ZMod q) * (n : ℂ) ^ (-s)) -
          E (N : ℝ) * (N : ℂ) ^ (-s) +
          (μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1) +
          s * ∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)‖
      ≤ (‖∑ n ∈ Finset.Icc 1 N, (1 : DirichletCharacter ℂ q) (n : ZMod q) * (n : ℂ) ^ (-s)‖ +
          ‖E (N : ℝ) * (N : ℂ) ^ (-s)‖) +
          ‖(μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1)‖ +
          ‖s * ∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (Real.log (N : ℝ) + 1 + 1) + 1 + 1 := by linarith
    _ ≤ 6 * L := by linarith

/-- Real-axis lower bounds on `riemannZeta (σ : ℂ)` for `σ > 1`:
`1 / (σ - 1) ≤ (riemannZeta σ).re`, `1 ≤ (riemannZeta σ).re`, and `(riemannZeta σ).im = 0`. -/
theorem riemannZeta_real_ge {σ : ℝ} (hσ : 1 < σ) :
    1 / (σ - 1) ≤ (riemannZeta (σ : ℂ)).re ∧
    1 ≤ (riemannZeta (σ : ℂ)).re ∧
    (riemannZeta (σ : ℂ)).im = 0 := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have hzeta : riemannZeta (σ : ℂ) =
      ((∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [← LSeries_one_eq_riemannZeta hs, LSeries, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp [LSeries.term_zero]
    · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      simp only [hn, ↓reduceIte]
      have hcpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
      rw [LSeries.term_of_ne_zero hn, Pi.one_apply, hcpow, ← Complex.ofReal_one,
        ← Complex.ofReal_div, one_div, ← Real.rpow_neg hn0.le]
  have hsum : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) := by
    have h1 := Real.summable_nat_rpow_inv.mpr hσ
    refine h1.congr fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp [Real.zero_rpow (by linarith : σ ≠ 0)]
    · simp only [hn, ↓reduceIte, Real.rpow_neg (Nat.cast_nonneg n)]
  have hnn : ∀ n : ℕ, 0 ≤ (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) := fun n => by
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [hzeta, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, ?_, rfl⟩
  · -- Lower bound `≥ 1 / (σ - 1)` via telescoping MVT on `n^{-σ} ≥ (n^{1-σ} - (n+1)^{1-σ}) / (σ - 1)`
    have hsum_ge : ∀ M : ℕ, 1 ≤ M →
        (1 - ((M + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) ≤
          ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-σ) := by
      intro M hM
      induction M, hM using Nat.le_induction with
      | base =>
        have hstep : (1 - ((2 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) ≤ (1 : ℝ) ^ (-σ) := by
          have h12 : (1 : ℝ) < (2 : ℝ) := by norm_num
          have hcont : ContinuousOn (fun u : ℝ => -(u ^ (1 - σ))) (Set.Icc (1 : ℝ) 2) := by
            refine ContinuousOn.neg (ContinuousOn.rpow_const continuousOn_id fun u hu => ?_)
            exact Or.inl (zero_lt_one.trans_le hu.1).ne'
          have hderiv : ∀ u ∈ Set.Ioo (1 : ℝ) 2,
              HasDerivAt (fun t : ℝ => -(t ^ (1 - σ))) ((σ - 1) * u ^ (-σ)) u := by
            intro u hu
            have h := (Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl (zero_lt_one.trans hu.1).ne')).neg
            refine h.congr_deriv ?_
            rw [show (1 - σ) - 1 = -σ by ring]; ring
          obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun u : ℝ => -(u ^ (1 - σ)))
            (fun u => (σ - 1) * u ^ (-σ)) h12 hcont hderiv
          rw [show (2 : ℝ) - 1 = 1 by norm_num, div_one] at hslope
          have hle : (σ - 1) * c ^ (-σ) ≤ (σ - 1) * (1 : ℝ) ^ (-σ) := by
            refine mul_le_mul_of_nonneg_left ?_ (by linarith)
            exact Real.rpow_le_rpow_of_nonpos zero_lt_one hc.1.le (by linarith)
          rw [Real.one_rpow, mul_one] at hle
          rw [Real.one_rpow] at hslope
          rw [div_le_iff₀ (by linarith), Real.one_rpow, one_mul]
          norm_num at hslope ⊢
          linarith
        simpa using hstep
      | succ k hk ih =>
        have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
          ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnot : k + 1 ∉ Finset.Icc 1 k := by simp
        rw [hIcc, Finset.sum_insert hnot]
        have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
        have hlt : ((k + 1 : ℕ) : ℝ) < ((k + 2 : ℕ) : ℝ) := by push_cast; linarith
        have hcont : ContinuousOn (fun u : ℝ => -(u ^ (1 - σ)))
            (Set.Icc ((k + 1 : ℕ) : ℝ) ((k + 2 : ℕ) : ℝ)) := by
          refine ContinuousOn.neg (ContinuousOn.rpow_const continuousOn_id fun u hu => ?_)
          exact Or.inl (lt_of_lt_of_le hk1_pos hu.1).ne'
        have hderiv : ∀ u ∈ Set.Ioo ((k + 1 : ℕ) : ℝ) ((k + 2 : ℕ) : ℝ),
            HasDerivAt (fun t : ℝ => -(t ^ (1 - σ))) ((σ - 1) * u ^ (-σ)) u := by
          intro u hu
          have h := (Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl (hk1_pos.trans hu.1).ne')).neg
          refine h.congr_deriv ?_
          rw [show (1 - σ) - 1 = -σ by ring]; ring
        obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun u : ℝ => -(u ^ (1 - σ)))
          (fun u => (σ - 1) * u ^ (-σ)) hlt hcont hderiv
        have hden : ((k + 2 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ) = 1 := by push_cast; ring
        rw [hden, div_one] at hslope
        have hle : (σ - 1) * c ^ (-σ) ≤ (σ - 1) * ((k + 1 : ℕ) : ℝ) ^ (-σ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          exact Real.rpow_le_rpow_of_nonpos hk1_pos hc.1.le (by linarith)
        have hstep : (((k + 1 : ℕ) : ℝ) ^ (1 - σ) - ((k + 2 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) ≤
            ((k + 1 : ℕ) : ℝ) ^ (-σ) := by
          rw [div_le_iff₀ (by linarith)]; linarith
        have halg : (1 - ((k + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) +
            (((k + 1 : ℕ) : ℝ) ^ (1 - σ) - ((k + 2 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) =
            (1 - ((k + 2 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) := by
          field_simp [(by linarith : σ - 1 ≠ 0)]; ring
        have hcast2 : ((k + 1 + 1 : ℕ) : ℝ) = ((k + 2 : ℕ) : ℝ) := by norm_cast
        rw [hcast2]
        linarith
    have hpartial : ∀ M : ℕ, 1 ≤ M →
        (1 - ((M + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) ≤
          ∑ n ∈ Finset.range (M + 1), (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) := by
      intro M hM
      have hsplit : Finset.range (M + 1) = insert 0 (Finset.Icc 1 M) := by
        ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hsplit, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 M)]
      simp only [↓reduceIte, zero_add]
      have hcongr : ∑ n ∈ Finset.Icc 1 M, (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) =
          ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-σ) :=
        Finset.sum_congr rfl fun n hn => by
          have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
          simp [hn0]
      rw [hcongr]
      exact hsum_ge M hM
    have hlimL : Tendsto (fun M : ℕ => ((1 : ℝ) - ((M + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1))
        atTop (𝓝 ((1 : ℝ) / (σ - 1))) := by
      have h0 : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ) ^ (-(σ - 1))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by linarith : 0 < σ - 1)).comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      have h0' : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ) ^ (1 - σ)) atTop (𝓝 0) := by
        simpa only [show 1 - σ = -(σ - 1) by ring] using h0
      have h1 : Tendsto (fun M : ℕ => ((1 : ℝ) - ((M + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1))
          atTop (𝓝 (((1 : ℝ) - 0) / (σ - 1))) :=
        (tendsto_const_nhds.sub h0').div_const (σ - 1)
      simpa only [sub_zero] using h1
    have hlimR : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (M + 1),
        if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) atTop
        (𝓝 (∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ))) :=
      hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    exact le_of_tendsto_of_tendsto' hlimL hlimR fun M => by
      rcases Nat.eq_zero_or_pos M with rfl | hM
      · have hle : (1 - ((1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) = 0 := by simp
        rw [hle]
        exact Finset.sum_nonneg fun n _ => hnn n
      · exact hpartial M hM
  · -- Lower bound `≥ 1` from the `n = 1` term
    have h1 := hsum.le_tsum 1 (fun n _ => hnn n)
    simpa using h1

/-- Upper bound on `-deriv riemannZeta (σ : ℂ)` for real `σ > 1`:
`(-deriv riemannZeta σ).re ≤ 1 / (σ - 1) ^ 2 + 2` and `(-deriv riemannZeta σ).im = 0`. -/
theorem neg_deriv_riemannZeta_real_le {σ : ℝ} (hσ : 1 < σ) :
    (-deriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) ^ 2 + 2 ∧
    (-deriv riemannZeta (σ : ℂ)).im = 0 := by
  let a : ℕ → ℝ := fun n => if n = 0 then 0 else 1
  have ha0 : a 0 = 0 := rfl
  have hconv : ∀ x : ℝ, 1 < x → LSeriesSummable (fun n => (a n : ℂ)) (x : ℂ) := by
    intro x hx
    have h1 : LSeriesSummable (1 : ℕ → ℂ) (x : ℂ) :=
      LSeriesSummable_one_iff.mpr (by simpa using hx)
    refine h1.congr fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp [LSeries.term_zero]
    · simp [a, hn]
  have hEv : riemannZeta =ᶠ[𝓝 (σ : ℂ)] Stage3RealAnalyticLandau.dirSeries a := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by simpa using hσ : 1 < (σ : ℂ).re)] with z (hz : 1 < z.re)
    rw [Stage3RealAnalyticLandau.dirSeries_eq_LSeries, ← LSeries_one_eq_riemannZeta hz]
    unfold LSeries
    refine tsum_congr fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp [LSeries.term_zero]
    · simp [a, hn]
  have hderiv_eq : -deriv riemannZeta (σ : ℂ) =
      ((∑' n : ℕ, a n * Real.log (n : ℝ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    have h1 := Stage3RealAnalyticLandau.alternating_iteratedDeriv_dirSeries_real ha0 hconv hσ 1
    simp only [pow_one, iteratedDeriv_one, neg_mul, one_mul] at h1
    rw [hEv.deriv_eq]
    exact h1
  rw [hderiv_eq, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  -- Compare `∑_{n=1}^M g(n)` against `∫_1^∞ g(u) du + 2` for unimodal `g(u) = (log u) u^{-σ}`
  let g : ℝ → ℝ := fun u => Real.log u * u ^ (-σ)
  have hg_nn : ∀ u : ℝ, 1 ≤ u → 0 ≤ g u := fun u hu =>
    mul_nonneg (Real.log_nonneg hu) (Real.rpow_nonneg (by linarith) _)
  have hg_le1 : ∀ u : ℝ, 1 ≤ u → g u ≤ 1 := by
    intro u hu
    have hu0 : 0 < u := zero_lt_one.trans_le hu
    have hlog := Real.log_le_rpow_div hu0.le (by linarith : 0 < σ)
    have hmul : u ^ σ * u ^ (-σ) = 1 := by
      rw [← Real.rpow_add hu0, add_neg_cancel, Real.rpow_zero]
    calc g u = Real.log u * u ^ (-σ) := rfl
      _ ≤ (u ^ σ / σ) * u ^ (-σ) := mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hu0.le _)
      _ = (u ^ σ * u ^ (-σ)) / σ := by ring
      _ = 1 / σ := by rw [hmul]
      _ ≤ 1 := (div_le_one (by linarith)).mpr hσ.le
  have hg_deriv : ∀ u : ℝ, 0 < u →
      HasDerivAt g ((1 - σ * Real.log u) * u ^ (-σ - 1)) u := by
    intro u hu
    have h1 := (Real.hasDerivAt_log hu.ne').mul (Real.hasDerivAt_rpow_const (p := -σ) (Or.inl hu.ne'))
    refine h1.congr_deriv ?_
    have hpow : u⁻¹ * u ^ (-σ) = u ^ (-σ - 1) := by
      rw [← Real.rpow_neg_one u, ← Real.rpow_add hu]; congr 1; ring
    calc u⁻¹ * u ^ (-σ) + Real.log u * (-σ * u ^ (-σ - 1))
        = u ^ (-σ - 1) - σ * Real.log u * u ^ (-σ - 1) := by rw [hpow]; ring
      _ = (1 - σ * Real.log u) * u ^ (-σ - 1) := by ring
  set u₀ : ℝ := Real.exp (1 / σ)
  have hu₀_gt1 : 1 < u₀ := Real.one_lt_exp_iff.mpr (by positivity)
  have hg_mono : MonotoneOn g (Set.Icc (1 : ℝ) u₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 1 u₀) ?_ ?_ ?_
    · refine ContinuousOn.mul ?_ ?_
      · exact Real.continuousOn_log.mono fun u hu => (zero_lt_one.trans_le hu.1).ne'
      · exact ContinuousOn.rpow_const continuousOn_id fun u hu => Or.inl (zero_lt_one.trans_le hu.1).ne'
    · intro u hu
      exact (hg_deriv u (zero_lt_one.trans_le (interior_subset hu).1)).differentiableAt.differentiableWithinAt
    · intro u hu
      have huI : u ∈ Set.Icc (1 : ℝ) u₀ := interior_subset hu
      have hu0 : 0 < u := zero_lt_one.trans_le huI.1
      rw [(hg_deriv u hu0).deriv]
      have hlog_le : Real.log u ≤ 1 / σ := by
        have := Real.log_le_log hu0 huI.2
        rwa [Real.log_exp] at this
      have h1 : 0 ≤ 1 - σ * Real.log u := by
        have : σ * Real.log u ≤ σ * (1 / σ) := mul_le_mul_of_nonneg_left hlog_le (by linarith)
        rw [mul_one_div_cancel (by linarith : σ ≠ 0)] at this
        linarith
      exact mul_nonneg h1 (Real.rpow_nonneg hu0.le _)
  have hg_anti : AntitoneOn g (Set.Ici u₀) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici u₀) ?_ ?_ ?_
    · refine ContinuousOn.mul ?_ ?_
      · exact Real.continuousOn_log.mono fun u hu => (zero_lt_one.trans (hu₀_gt1.trans_le hu)).ne'
      · exact ContinuousOn.rpow_const continuousOn_id fun u hu =>
          Or.inl (zero_lt_one.trans (hu₀_gt1.trans_le hu)).ne'
    · intro u hu
      exact (hg_deriv u (zero_lt_one.trans (hu₀_gt1.trans_le (interior_subset hu)))).differentiableAt.differentiableWithinAt
    · intro u hu
      have huI : u₀ ≤ u := interior_subset hu
      have hu0 : 0 < u := zero_lt_one.trans (hu₀_gt1.trans_le huI)
      rw [(hg_deriv u hu0).deriv]
      have hlog_ge : 1 / σ ≤ Real.log u := by
        have := Real.log_le_log (zero_lt_one.trans hu₀_gt1) huI
        rwa [Real.log_exp] at this
      have h1 : 1 - σ * Real.log u ≤ 0 := by
        have : σ * (1 / σ) ≤ σ * Real.log u := mul_le_mul_of_nonneg_left hlog_ge (by linarith)
        rw [mul_one_div_cancel (by linarith : σ ≠ 0)] at this
        linarith
      exact mul_nonpos_of_nonpos_of_nonneg h1 (Real.rpow_nonneg hu0.le _)
  have hg_int : IntegrableOn g (Ioi (1 : ℝ)) := by
    have hdom : IntegrableOn (fun t : ℝ => ((σ - 1) / 2)⁻¹ * t ^ (-1 - (σ - 1) / 2)) (Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
    refine hdom.mono' ?_ ?_
    · exact (Real.measurable_log.mul (measurable_id.pow_const (-σ))).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := zero_lt_one.trans ht
      have hlog := Real.log_le_rpow_div ht0.le (by linarith : 0 < (σ - 1) / 2)
      dsimp only [g]
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn t ht.le)]
      have hpow : t ^ ((σ - 1) / 2) * t ^ (-σ) = t ^ (-1 - (σ - 1) / 2) := by
        rw [← Real.rpow_add ht0]; congr 1; ring
      calc Real.log t * t ^ (-σ)
          ≤ (t ^ ((σ - 1) / 2) / ((σ - 1) / 2)) * t ^ (-σ) :=
            mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg ht0.le _)
        _ = ((σ - 1) / 2)⁻¹ * (t ^ ((σ - 1) / 2) * t ^ (-σ)) := by ring
        _ = ((σ - 1) / 2)⁻¹ * t ^ (-1 - (σ - 1) / 2) := by rw [hpow]
  have hg_eval : ∫ u in Ioi (1 : ℝ), g u = 1 / (σ - 1) ^ 2 := by
    have hpt : g = fun u : ℝ => Real.log u * u ^ (-(σ - 1) - 1) := by
      funext u; dsimp only [g]; congr 2; ring
    rw [hpt, integral_Ioi_log_mul_rpow le_rfl (by linarith : 0 < σ - 1)]
    simp
  have hsum_real : Summable (fun n : ℕ => a n * Real.log (n : ℝ) * (n : ℝ) ^ (-σ)) := by
    have h := Stage3RealAnalyticLandau.summable_log_pow_mul_rpow ha0
      (fun n => by dsimp only [a]; split_ifs <;> norm_num) hconv hσ 1
    simpa only [pow_one] using h
  refine hsum_real.tsum_le_of_sum_range_le fun N => ?_
  -- Bound partial sum `∑_{n ∈ range N} a n * log n * n^{-σ} ≤ ∫_{Ioi 1} g + 2`
  set k : ℕ := ⌊u₀⌋₊
  have hk1 : 1 ≤ k := Nat.le_floor (by exact_mod_cast hu₀_gt1.le)
  have hk_le : (k : ℝ) ≤ u₀ := Nat.floor_le (by linarith)
  have hu₀_lt : u₀ < ((k + 1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one u₀
  have hsum_eq : ∑ n ∈ Finset.range N, a n * Real.log (n : ℝ) * (n : ℝ) ^ (-σ) =
      ∑ n ∈ Finset.Icc 1 (N - 1), g (n : ℝ) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hsp : Finset.range N = insert 0 (Finset.Icc 1 (N - 1)) := by
        ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hsp, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 (N - 1))]
      simp only [a, ↓reduceIte, zero_mul, zero_add]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
      simp [g, hn0]
  rw [hsum_eq, ← hg_eval]
  -- Partition `Icc 1 (N - 1)` into `n < k`, `n ∈ {k, k + 1}`, and `k + 2 ≤ n`
  set M := N - 1
  have hpart :
      ∑ n ∈ Finset.Icc 1 M, g (n : ℝ) ≤
        (∑ n ∈ Finset.Icc 1 (min M (k - 1)), g (n : ℝ)) +
        (∑ n ∈ Finset.Icc k (k + 1), g (n : ℝ)) +
        (∑ n ∈ Finset.Icc (k + 2) M, g (n : ℝ)) := by
    have hsub : Finset.Icc 1 M ⊆
        (Finset.Icc 1 (min M (k - 1)) ∪ Finset.Icc k (k + 1)) ∪ Finset.Icc (k + 2) M := by
      intro n hn
      simp only [Finset.mem_Icc, Finset.mem_union] at hn ⊢
      omega
    have hd1 : Disjoint (Finset.Icc 1 (min M (k - 1))) (Finset.Icc k (k + 1)) := by
      rw [Finset.disjoint_left]; intro n h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
    have hd2 : Disjoint (Finset.Icc 1 (min M (k - 1)) ∪ Finset.Icc k (k + 1)) (Finset.Icc (k + 2) M) := by
      rw [Finset.disjoint_left]; intro n h1 h2; simp only [Finset.mem_union, Finset.mem_Icc] at h1 h2; omega
    calc ∑ n ∈ Finset.Icc 1 M, g (n : ℝ)
        ≤ ∑ n ∈ (Finset.Icc 1 (min M (k - 1)) ∪ Finset.Icc k (k + 1)) ∪ Finset.Icc (k + 2) M, g (n : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => by
            apply hg_nn
            simp only [Finset.mem_union, Finset.mem_Icc] at hn
            exact_mod_cast (by omega : 1 ≤ n)
      _ = (∑ n ∈ Finset.Icc 1 (min M (k - 1)), g (n : ℝ)) +
            (∑ n ∈ Finset.Icc k (k + 1), g (n : ℝ)) +
            ∑ n ∈ Finset.Icc (k + 2) M, g (n : ℝ) := by
          rw [Finset.sum_union hd2, Finset.sum_union hd1]
  -- Middle 2 terms `≤ 2`
  have hmid : ∑ n ∈ Finset.Icc k (k + 1), g (n : ℝ) ≤ 2 := by
    have hpair : Finset.Icc k (k + 1) = {k, k + 1} := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    rw [hpair, Finset.sum_pair (by omega)]
    have h1 := hg_le1 (k : ℝ) (by exact_mod_cast hk1)
    have h2 := hg_le1 ((k + 1 : ℕ) : ℝ) (by exact_mod_cast (by omega : 1 ≤ k + 1))
    linarith
  -- Left sum `≤ ∫ u in Ioc 1 k, g u`
  have hleft : ∑ n ∈ Finset.Icc 1 (min M (k - 1)), g (n : ℝ) ≤ ∫ u in Ioc (1 : ℝ) (k : ℝ), g u := by
    have hstep : ∀ m : ℕ, m ≤ k - 1 →
        ∑ n ∈ Finset.Icc 1 m, g (n : ℝ) ≤ ∫ u in (1 : ℝ)..((m + 1 : ℕ) : ℝ), g u := by
      intro m hm
      induction m with
      | zero => simp
      | succ m ih =>
        have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
          ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnot : m + 1 ∉ Finset.Icc 1 m := by simp
        rw [hIcc, Finset.sum_insert hnot]
        have hm1_ge1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
        have hm2_le : ((m + 2 : ℕ) : ℝ) ≤ u₀ :=
          le_trans (by exact_mod_cast (by omega : m + 2 ≤ k)) hk_le
        have hsub1 : Ioc (1 : ℝ) ((m + 1 : ℕ) : ℝ) ⊆ Ioi (1 : ℝ) := Ioc_subset_Ioi_self
        have hsub2 : Ioc ((m + 1 : ℕ) : ℝ) ((m + 2 : ℕ) : ℝ) ⊆ Ioi (1 : ℝ) :=
          Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hm1_ge1)
        have hint1 : IntervalIntegrable g volume (1 : ℝ) ((m + 1 : ℕ) : ℝ) := by
          rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hm1_ge1]
          exact hg_int.mono_set hsub1
        have hint2 : IntervalIntegrable g volume ((m + 1 : ℕ) : ℝ) ((m + 2 : ℕ) : ℝ) := by
          rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by push_cast; linarith)]
          exact hg_int.mono_set hsub2
        have hbox : g ((m + 1 : ℕ) : ℝ) ≤ ∫ u in ((m + 1 : ℕ) : ℝ)..((m + 2 : ℕ) : ℝ), g u := by
          have hconst : g ((m + 1 : ℕ) : ℝ) = ∫ _u in ((m + 1 : ℕ) : ℝ)..((m + 2 : ℕ) : ℝ), g ((m + 1 : ℕ) : ℝ) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
            push_cast; ring
          rw [hconst]
          refine intervalIntegral.integral_mono_on (by push_cast; linarith)
            intervalIntegrable_const hint2 fun u hu => ?_
          exact hg_mono ⟨hm1_ge1, le_trans (by push_cast; linarith) hm2_le⟩
            ⟨hm1_ge1.trans hu.1, hu.2.trans hm2_le⟩ hu.1
        rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
        linarith [ih (by omega)]
    have h1 := hstep (min M (k - 1)) (min_le_right M (k - 1))
    rw [intervalIntegral.integral_of_le (by exact_mod_cast (by omega : 1 ≤ min M (k - 1) + 1))] at h1
    refine h1.trans (setIntegral_mono_set (hg_int.mono_set Ioc_subset_Ioi_self) ?_ ?_)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => hg_nn u hu.1.le
    · exact Eventually.of_forall fun u hu =>
        ⟨hu.1, hu.2.trans (by exact_mod_cast (by omega : min M (k - 1) + 1 ≤ k))⟩
  -- Right sum `≤ ∫ u in Ioi (k + 1), g u`
  have hright : ∑ n ∈ Finset.Icc (k + 2) M, g (n : ℝ) ≤ ∫ u in Ioi ((k + 1 : ℕ) : ℝ), g u := by
    by_cases hM : M < k + 2
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      exact setIntegral_nonneg measurableSet_Ioi fun u hu =>
        hg_nn u (le_trans (by exact_mod_cast (by omega : 1 ≤ k + 1)) hu.le)
    · have hM_ge : k + 2 ≤ M := by omega
      have hstep : ∀ m : ℕ, k + 2 ≤ m →
          ∑ n ∈ Finset.Icc (k + 2) m, g (n : ℝ) ≤ ∫ u in ((k + 1 : ℕ) : ℝ)..(m : ℝ), g u := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base =>
          have hIcc : Finset.Icc (k + 2) (k + 2) = {k + 2} := Finset.Icc_self _
          rw [hIcc, Finset.sum_singleton]
          have hsub : Ioc ((k + 1 : ℕ) : ℝ) ((k + 2 : ℕ) : ℝ) ⊆ Ioi (1 : ℝ) :=
            Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by exact_mod_cast (by omega : 1 ≤ k + 1)))
          have hint : IntervalIntegrable g volume ((k + 1 : ℕ) : ℝ) ((k + 2 : ℕ) : ℝ) := by
            rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by push_cast; linarith)]
            exact hg_int.mono_set hsub
          have hconst : g ((k + 2 : ℕ) : ℝ) = ∫ _u in ((k + 1 : ℕ) : ℝ)..((k + 2 : ℕ) : ℝ), g ((k + 2 : ℕ) : ℝ) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; push_cast; ring
          rw [hconst]
          refine intervalIntegral.integral_mono_on (by push_cast; linarith)
            intervalIntegrable_const hint fun u hu => ?_
          exact hg_anti (hu₀_lt.le.trans hu.1) (hu₀_lt.le.trans (by push_cast; linarith)) hu.2
        | succ m hm ih =>
          have hIcc : Finset.Icc (k + 2) (m + 1) = insert (m + 1) (Finset.Icc (k + 2) m) := by
            ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          have hnot : m + 1 ∉ Finset.Icc (k + 2) m := by simp
          rw [hIcc, Finset.sum_insert hnot]
          have hsub1 : Ioc ((k + 1 : ℕ) : ℝ) (m : ℝ) ⊆ Ioi (1 : ℝ) :=
            Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by exact_mod_cast (by omega : 1 ≤ k + 1)))
          have hsub2 : Ioc (m : ℝ) ((m + 1 : ℕ) : ℝ) ⊆ Ioi (1 : ℝ) :=
            Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by exact_mod_cast (by omega : 1 ≤ m)))
          have hint1 : IntervalIntegrable g volume ((k + 1 : ℕ) : ℝ) (m : ℝ) := by
            rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast (by omega : k + 1 ≤ m))]
            exact hg_int.mono_set hsub1
          have hint2 : IntervalIntegrable g volume (m : ℝ) ((m + 1 : ℕ) : ℝ) := by
            rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by push_cast; linarith)]
            exact hg_int.mono_set hsub2
          have hbox : g ((m + 1 : ℕ) : ℝ) ≤ ∫ u in (m : ℝ)..((m + 1 : ℕ) : ℝ), g u := by
            have hconst : g ((m + 1 : ℕ) : ℝ) = ∫ _u in (m : ℝ)..((m + 1 : ℕ) : ℝ), g ((m + 1 : ℕ) : ℝ) := by
              rw [intervalIntegral.integral_const, smul_eq_mul]; push_cast; ring
            rw [hconst]
            refine intervalIntegral.integral_mono_on (by push_cast; linarith)
              intervalIntegrable_const hint2 fun u hu => ?_
            have hm_ge_u0 : u₀ ≤ (m : ℝ) := le_trans hu₀_lt.le (by exact_mod_cast (by omega : k + 1 ≤ m))
            exact hg_anti (hm_ge_u0.trans hu.1) (hm_ge_u0.trans (by push_cast; linarith)) hu.2
          rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
          linarith
      have h1 := hstep M hM_ge
      rw [intervalIntegral.integral_of_le (by exact_mod_cast (by omega : k + 1 ≤ M))] at h1
      refine h1.trans (setIntegral_mono_set (hg_int.mono_set (Ioi_subset_Ioi (by exact_mod_cast (by omega : 1 ≤ k + 1)))) ?_ ?_)
      · exact ae_restrict_of_forall_mem measurableSet_Ioi fun u hu =>
          hg_nn u (le_trans (by exact_mod_cast (by omega : 1 ≤ k + 1)) hu.le)
      · exact Eventually.of_forall fun u hu => hu.1
  -- Combine disjoint integrals `Ioc 1 k` and `Ioi (k + 1)` inside `Ioi 1`
  have hint_comb :
      (∫ u in Ioc (1 : ℝ) (k : ℝ), g u) + (∫ u in Ioi ((k + 1 : ℕ) : ℝ), g u) ≤
        ∫ u in Ioi (1 : ℝ), g u := by
    have hdisj : Disjoint (Ioc (1 : ℝ) (k : ℝ)) (Ioi ((k + 1 : ℕ) : ℝ)) := by
      rw [Set.disjoint_left]
      intro u hu1 hu2
      simp only [Set.mem_Ioc, Set.mem_Ioi] at hu1 hu2
      have : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
      linarith [hu1.2, hu2]
    have hsubU : Ioc (1 : ℝ) (k : ℝ) ∪ Ioi ((k + 1 : ℕ) : ℝ) ⊆ Ioi (1 : ℝ) :=
      Set.union_subset Ioc_subset_Ioi_self
        (Ioi_subset_Ioi (by exact_mod_cast (by omega : 1 ≤ k + 1)))
    rw [← setIntegral_union hdisj measurableSet_Ioi
      (hg_int.mono_set Ioc_subset_Ioi_self)
      (hg_int.mono_set (Ioi_subset_Ioi (by exact_mod_cast (by omega : 1 ≤ k + 1))))]
    refine setIntegral_mono_set hg_int ?_ (Eventually.of_forall fun u hu => hsubU hu)
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => hg_nn u hu.le
  linarith

/-- **Unconditional Real-Axis Logarithmic-Derivative Upper Bound on `riemannZeta`**:
for ALL `σ > 1`, `(-deriv riemannZeta σ / riemannZeta σ).re ≤ 1 / (σ - 1) + 3`. -/
theorem negLogDerivZeta_re_le_inv_sub_one_add {σ : ℝ} (hσ : 1 < σ) :
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 3 := by
  obtain ⟨hz_inv, hz_1, hz_im⟩ := riemannZeta_real_ge hσ
  obtain ⟨hd_le, hd_im⟩ := neg_deriv_riemannZeta_real_le hσ
  have hz_pos : 0 < (riemannZeta (σ : ℂ)).re := by linarith
  have hz_eq : riemannZeta (σ : ℂ) = (((riemannZeta (σ : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [hz_im])
  have hd_eq : -deriv riemannZeta (σ : ℂ) = (((-deriv riemannZeta (σ : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [hd_im])
  have hre_div :
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re =
        (-deriv riemannZeta (σ : ℂ)).re / (riemannZeta (σ : ℂ)).re := by
    conv_lhs => rw [hd_eq, hz_eq, ← Complex.ofReal_div]
    simp
  rw [hre_div]
  have hd_nn : 0 ≤ (-deriv riemannZeta (σ : ℂ)).re := by
    have hnn := Stage3ZeroFreeRegion.negLogDerivZeta_re_nonneg hσ
    unfold Stage3ZeroFreeRegion.negLogDerivZeta at hnn
    rw [hre_div] at hnn
    exact (div_nonneg_iff.mp hnn).elim (fun h => h.1) (fun h => by linarith)
  rcases le_or_gt σ 2 with hle2 | hgt2
  · have hpos_inv : 0 < 1 / (σ - 1) := by positivity
    calc (-deriv riemannZeta (σ : ℂ)).re / (riemannZeta (σ : ℂ)).re
        ≤ (1 / (σ - 1) ^ 2 + 2) / (1 / (σ - 1)) :=
          div_le_div₀ (by positivity) hd_le hpos_inv hz_inv
      _ = 1 / (σ - 1) + 2 * (σ - 1) := by
          field_simp [(by linarith : σ - 1 ≠ 0)]
      _ ≤ 1 / (σ - 1) + 3 := by linarith
  · have hinv2 : 1 / (σ - 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    calc (-deriv riemannZeta (σ : ℂ)).re / (riemannZeta (σ : ℂ)).re
        ≤ (1 / (σ - 1) ^ 2 + 2) / 1 :=
          div_le_div₀ (by positivity) hd_le zero_lt_one hz_1
      _ = 1 / (σ - 1) ^ 2 + 2 := div_one _
      _ ≤ 1 / (σ - 1) + 3 := by
          have : 0 < 1 / (σ - 1) := by positivity
          linarith

/-- **Unconditional Right-of-1 Logarithmic-Derivative Domination by `-ζ'/ζ`**:
for EVERY `q ≥ 1`, EVERY `χ : DirichletCharacter ℂ q`, EVERY `σ > 1`, and EVERY `t : ℝ`:
`‖-deriv (LFunction χ) (σ + I * t) / LFunction χ (σ + I * t)‖ ≤ (-deriv riemannZeta σ / riemannZeta σ).re`. -/
theorem norm_negLogDerivL_le_negLogDerivZeta_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖-deriv (LFunction χ) ((σ : ℂ) + I * (t : ℂ)) / LFunction χ ((σ : ℂ) + I * (t : ℂ))‖ ≤
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
  have hs : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ]
  have hs0 : 1 < (σ : ℂ).re := by simpa using hσ
  have hL : -deriv (LFunction χ) ((σ : ℂ) + I * (t : ℂ)) / LFunction χ ((σ : ℂ) + I * (t : ℂ)) =
      LSeries (fun n => χ (n : ZMod q) * (Λ n : ℂ)) ((σ : ℂ) + I * (t : ℂ)) :=
    Stage3ZeroFreeRegion.negLogDerivL_eq_LSeries χ hs
  have hZ : -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) =
      LSeries (fun n => (Λ n : ℂ)) (σ : ℂ) :=
    Stage3ZeroFreeRegion.negLogDerivZeta_eq_LSeries hs0
  rw [hL, hZ]
  have hsumL : LSeriesSummable (fun n => χ (n : ZMod q) * (Λ n : ℂ)) ((σ : ℂ) + I * (t : ℂ)) :=
    χ.LSeriesSummable_twist_vonMangoldt hs
  have hsumZ : LSeriesSummable (fun n => (Λ n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs0
  have hZ_re :
      (LSeries (fun n => (Λ n : ℂ)) (σ : ℂ)).re =
        ∑' n : ℕ, (LSeries.term (fun n => (Λ n : ℂ)) (σ : ℂ) n).re := by
    unfold LSeries
    simpa [Complex.reCLM_apply] using Complex.reCLM.map_tsum hsumZ
  have hsumZ_re : Summable (fun n : ℕ => (LSeries.term (fun n => (Λ n : ℂ)) (σ : ℂ) n).re) :=
    Complex.reCLM.summable hsumZ
  rw [hZ_re]
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hsumL.norm).trans ?_
  refine hsumL.norm.tsum_le_tsum (fun n => ?_) hsumZ_re
  by_cases hn : n = 0
  · subst hn; simp [LSeries.term_zero]
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.norm_natCast_cpow_of_pos hn_pos]
    have hre1 : ((σ : ℂ) + I * (t : ℂ)).re = σ := by simp
    have hcpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hnR.le]
    rw [hre1, hcpow, ← Complex.ofReal_div, Complex.ofReal_re]
    have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    exact div_le_div_of_nonneg_right
      (by simpa using mul_le_mul_of_nonneg_right (χ.norm_le_one (n : ZMod q)) hΛ)
      (Real.rpow_nonneg hnR.le σ)

/-- **Combined Unconditional Right-of-1 Logarithmic-Derivative Bound**:
for EVERY `q ≥ 1`, EVERY `χ : DirichletCharacter ℂ q`, EVERY `σ > 1`, and EVERY `t : ℝ`:
`‖-deriv (LFunction χ) (σ + I * t) / LFunction χ (σ + I * t)‖ ≤ 1 / (σ - 1) + 3`. -/
theorem norm_negLogDerivL_le_inv_sub_one_add {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖-deriv (LFunction χ) ((σ : ℂ) + I * (t : ℂ)) / LFunction χ ((σ : ℂ) + I * (t : ℂ))‖ ≤
      1 / (σ - 1) + 3 :=
  (norm_negLogDerivL_le_negLogDerivZeta_re χ hσ t).trans (negLogDerivZeta_re_le_inv_sub_one_add hσ)

/-! ## Section 3: Quantitative 1-Line Lower Bound & Unconditional Concrete Zero-Free Region -/

/-- Horizontal Mean-Value-Theorem Lipchitz bound for `LFunction χ` on `1 - 1 / L ≤ σ₁ ≤ σ₂ ≤ 2`:
`‖L(χ, σ₂ + i t) - L(χ, σ₁ + i t)‖ ≤ (σ₂ - σ₁) * (288 * (log (q (|t| + 2)))²)`. -/
theorem norm_LFunction_sub_le_of_strip {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {σ₁ σ₂ t : ℝ}
    (hσ₁ : 1 - (Real.log ((q : ℝ) * (|t| + 2)))⁻¹ ≤ σ₁) (hσ₁₂ : σ₁ ≤ σ₂) (hσ₂ : σ₂ ≤ 2) :
    ‖LFunction χ ((σ₂ : ℂ) + I * (t : ℂ)) - LFunction χ ((σ₁ : ℂ) + I * (t : ℂ))‖ ≤
      (σ₂ - σ₁) * (288 * (Real.log ((q : ℝ) * (|t| + 2))) ^ 2) := by
  let f : ℝ → ℂ := fun u => LFunction χ ((u : ℂ) + I * (t : ℂ))
  have hf_deriv : ∀ u : ℝ,
      HasDerivAt f (deriv (LFunction χ) ((u : ℂ) + I * (t : ℂ))) u := by
    intro u
    have hL : HasDerivAt (LFunction χ) (deriv (LFunction χ) ((u : ℂ) + I * (t : ℂ)))
        ((u : ℂ) + I * (t : ℂ)) :=
      (DirichletCharacter.differentiable_LFunction hχ ((u : ℂ) + I * (t : ℂ))).hasDerivAt
    have hshift := hL.comp (u : ℂ) ((hasDerivAt_id (u : ℂ)).add_const (I * (t : ℂ)))
    rw [mul_one] at hshift
    exact hshift.comp_ofReal
  have hbd := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := f)
    (s := Set.Icc σ₁ σ₂) (C := 288 * (Real.log ((q : ℝ) * (|t| + 2))) ^ 2)
    (fun u _ => (hf_deriv u).differentiableAt)
    (fun u hu => by
      rw [(hf_deriv u).deriv]
      have h := norm_deriv_LFunction_le_log_sq hχ (s := (u : ℂ) + I * (t : ℂ))
        (by simp; linarith [hu.1]) (by simp; linarith [hu.2])
      simpa using h)
    (convex_Icc σ₁ σ₂) ⟨le_rfl, hσ₁₂⟩ ⟨hσ₁₂, le_rfl⟩
  have hnorm : ‖σ₂ - σ₁‖ = σ₂ - σ₁ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hσ₁₂)]
  rw [hnorm] at hbd
  simpa only [f, mul_comm] using hbd

/-- Explicit constant for the unconditional 1-line lower bound `c₁ / (log (q (|t| + 2))) ^ 7`. -/
def oneLineLowerConst : ℝ := 1 / (1536 * 288 ^ 3)

theorem oneLineLowerConst_pos : 0 < oneLineLowerConst := by
  unfold oneLineLowerConst; positivity

/-- **Unconditional Quantitative de la Vallée Poussin 1-Line Lower Bound (0 Assumptions!)**:
for EVERY `q : ℕ` (`[NeZero q]`), EVERY non-principal `χ : DirichletCharacter ℂ q` (`χ ≠ 1`),
and EVERY `t : ℝ`, whenever `χ ^ 2 ≠ 1` OR `1 ≤ |t|`:
`oneLineLowerConst / (Real.log (q * (|t| + 2))) ^ 7 ≤ ‖LFunction χ (1 + I * t)‖`. -/
theorem norm_LFunction_one_add_I_mul_ge {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {t : ℝ} (hcase : χ ^ 2 ≠ 1 ∨ 1 ≤ |t|) :
    oneLineLowerConst / (Real.log ((q : ℝ) * (|t| + 2))) ^ 7 ≤
      ‖LFunction χ (1 + I * (t : ℂ))‖ := by
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
  set L : ℝ := Real.log ((q : ℝ) * (|t| + 2))
  have hL : (1.38 : ℝ) < L := log_q_mul_abs_add_two_ge hq2 t
  have hL_pos : 0 < L := by linarith
  have hL_ge1 : 1 ≤ L := by linarith
  set a : ℝ := 1 / (1536 * 288 ^ 4)
  have ha_pos : 0 < a := by positivity
  have ha_le1 : a ≤ 1 := by dsimp only [a]; norm_num
  set x : ℝ := a / L ^ 9
  have hx_pos : 0 < x := div_pos ha_pos (pow_pos hL_pos 9)
  have hx_le1 : x ≤ 1 := by
    rw [div_le_one (pow_pos hL_pos 9)]
    exact ha_le1.trans (one_le_pow₀ hL_ge1)
  have htarget_eq : oneLineLowerConst / L ^ 7 = 288 * x * L ^ 2 := by
    dsimp only [oneLineLowerConst, x, a]
    field_simp [hL_pos.ne']
  rw [htarget_eq]
  by_contra hlt
  push Not at hlt
  -- MVT on `[1, 1 + x]` gives `‖L(χ, 1 + x + it)‖ < 2 * (288 * x * L^2)`
  have hmvt := norm_LFunction_sub_le_of_strip hχ (σ₁ := 1) (σ₂ := 1 + x) (t := t)
    (by linarith [inv_pos.mpr hL_pos]) (by linarith) (by linarith)
  have hsub_eq : (1 + x : ℝ) - 1 = x := by ring
  rw [hsub_eq] at hmvt
  have hcast1 : ((1 : ℝ) : ℂ) + I * (t : ℂ) = 1 + I * (t : ℂ) := by simp
  have hcastx : ((1 + x : ℝ) : ℂ) + I * (t : ℂ) = 1 + (x : ℂ) + I * (t : ℂ) := by push_cast; ring
  rw [hcast1, hcastx] at hmvt
  have hL_chi_lt : ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ < 2 * (288 * x * L ^ 2) := by
    have htri : ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ ≤
        ‖LFunction χ (1 + I * (t : ℂ))‖ +
          ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ)) - LFunction χ (1 + I * (t : ℂ))‖ := by
      have := norm_add_le (LFunction χ (1 + I * (t : ℂ)))
        (LFunction χ (1 + (x : ℂ) + I * (t : ℂ)) - LFunction χ (1 + I * (t : ℂ)))
      simpa using this
    linarith
  -- Upper bound on `‖L(1_q, 1 + x)‖ ≤ 2 / x`
  have hL1 : ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ≤ 2 / x :=
    norm_LFunction_one_real_le_two_div hx_pos hx_le1
  -- Upper bound on `‖L(χ², 1 + x + 2 i t)‖ ≤ 12 * L`
  have hL2 : ‖LFunction (χ ^ 2) (1 + (x : ℂ) + 2 * I * (t : ℂ))‖ ≤ 12 * L := by
    have harg : (1 + (x : ℂ) + 2 * I * (t : ℂ)) = ((1 + x : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ) := by
      push_cast; ring
    have hlog2t : Real.log ((q : ℝ) * (|2 * t| + 2)) ≤ 2 * L := by
      have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
      have hle : (q : ℝ) * (|2 * t| + 2) ≤ 2 * ((q : ℝ) * (|t| + 2)) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        nlinarith [abs_nonneg t]
      have h1 := Real.log_le_log (by positivity) hle
      have hmul : Real.log (2 * ((q : ℝ) * (|t| + 2))) = Real.log 2 + L :=
        Real.log_mul (by norm_num) (by positivity)
      have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
      linarith
    rcases hcase with hsq_ne | ht1
    · have hbd := norm_LFunction_le_log_of_one_le_re hsq_ne
        (s := 1 + (x : ℂ) + 2 * I * (t : ℂ)) (by simp [hx_pos.le]) (by simp; linarith)
      have him2 : (1 + (x : ℂ) + 2 * I * (t : ℂ)).im = 2 * t := by simp
      rw [him2] at hbd
      linarith
    · by_cases hsq_ne : χ ^ 2 ≠ 1
      · have hbd := norm_LFunction_le_log_of_one_le_re hsq_ne
          (s := 1 + (x : ℂ) + 2 * I * (t : ℂ)) (by simp [hx_pos.le]) (by simp; linarith)
        have him2 : (1 + (x : ℂ) + 2 * I * (t : ℂ)).im = 2 * t := by simp
        rw [him2] at hbd
        linarith
      · push Not at hsq_ne
        rw [hsq_ne, harg]
        have h2t : 1 ≤ |2 * t| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
        have hbd := norm_LFunction_one_strip_le (q := q) hq2 hx_pos hx_le1 h2t
        linarith
  -- Apply de la Vallée Poussin 3-4-1 inequality: `1 ≤ |L(1, 1+x)|³ |L(χ, 1+x+it)|⁴ |L(χ², 1+x+2it)|`
  have h341 := Stage2DirichletAP.norm_LFunction_three_four_one_ge_one χ hx_pos t
  simp only [norm_mul, norm_pow] at h341
  have hpow3 : ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ^ 3 ≤ (2 / x) ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg _) hL1 3
  have hpow4 : ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ ^ 4 < (2 * (288 * x * L ^ 2)) ^ 4 :=
    pow_lt_pow_left₀ hL_chi_lt (norm_nonneg _) (by norm_num)
  have hprod_lt :
      ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ^ 3 *
        ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ ^ 4 *
        ‖LFunction (χ ^ 2) (1 + (x : ℂ) + 2 * I * (t : ℂ))‖ <
      (2 / x) ^ 3 * (2 * (288 * x * L ^ 2)) ^ 4 * (12 * L) := by
    have h12 :
        ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ^ 3 *
          ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ ^ 4 <
        (2 / x) ^ 3 * (2 * (288 * x * L ^ 2)) ^ 4 := by
      have hpos3 : 0 < (2 / x) ^ 3 := by positivity
      calc ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ^ 3 *
              ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ ^ 4
          ≤ (2 / x) ^ 3 * ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ ^ 4 :=
            mul_le_mul_of_nonneg_right hpow3 (pow_nonneg (norm_nonneg _) 4)
        _ < (2 / x) ^ 3 * (2 * (288 * x * L ^ 2)) ^ 4 :=
            mul_lt_mul_of_pos_left hpow4 hpos3
    calc ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ^ 3 *
            ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ ^ 4 *
            ‖LFunction (χ ^ 2) (1 + (x : ℂ) + 2 * I * (t : ℂ))‖
        ≤ ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ^ 3 *
            ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ ^ 4 * (12 * L) :=
          mul_le_mul_of_nonneg_left hL2 (mul_nonneg (pow_nonneg (norm_nonneg _) 3) (pow_nonneg (norm_nonneg _) 4))
      _ < (2 / x) ^ 3 * (2 * (288 * x * L ^ 2)) ^ 4 * (12 * L) :=
          mul_lt_mul_of_pos_right h12 (by positivity)
  have hrhs_eq : (2 / x) ^ 3 * (2 * (288 * x * L ^ 2)) ^ 4 * (12 * L) = 1 := by
    dsimp only [x, a]
    field_simp [hL_pos.ne']
    ring
  linarith

/-- Explicit zero-free-region constant `c = 1 / (3072 * 288 ^ 4)`. -/
def zeroFreeConst : ℝ := 1 / (3072 * 288 ^ 4)

theorem zeroFreeConst_pos : 0 < zeroFreeConst := by
  unfold zeroFreeConst; positivity

/-- **UNCONDITIONAL CONCRETE ZERO-FREE REGION DIRECTLY ON MATHLIB'S `DirichletCharacter.LFunction`**
(general non-principal form, 0 assumptions):
for EVERY `q ≥ 1` (`[NeZero q]`), EVERY non-principal `χ : DirichletCharacter ℂ q` (`χ ≠ 1`),
and EVERY `s : ℂ` with `χ ^ 2 ≠ 1` OR `1 ≤ |s.im|`, if
`1 - zeroFreeConst / (Real.log (q * (|s.im| + 2))) ^ 9 ≤ s.re`,
then `DirichletCharacter.LFunction χ s ≠ 0`. -/
theorem LFunction_ne_zero_in_zeroFreeRegion {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hcase : χ ^ 2 ≠ 1 ∨ 1 ≤ |s.im|)
    (hs : 1 - zeroFreeConst / (Real.log ((q : ℝ) * (|s.im| + 2))) ^ 9 ≤ s.re) :
    LFunction χ s ≠ 0 := by
  by_cases hge1 : 1 ≤ s.re
  · exact Stage2DirichletAP.LFunction_ne_zero_of_one_le_re_bridge χ (Or.inl hχ) hge1
  · push Not at hge1
    have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
    set t : ℝ := s.im
    set L : ℝ := Real.log ((q : ℝ) * (|t| + 2))
    have hL : (1.38 : ℝ) < L := log_q_mul_abs_add_two_ge hq2 t
    have hL_pos : 0 < L := by linarith
    have hL_ge1 : 1 ≤ L := by linarith
    have hc_le1 : zeroFreeConst ≤ 1 := by unfold zeroFreeConst; norm_num
    have hdiv_le : zeroFreeConst / L ^ 9 ≤ L⁻¹ := by
      rw [inv_eq_one_div]
      have hpow : L ≤ L ^ 9 := by
        calc L = L ^ 1 := (pow_one L).symm
          _ ≤ L ^ 9 := pow_le_pow_right₀ hL_ge1 (by norm_num)
      exact div_le_div₀ zero_le_one hc_le1 hL_pos hpow
    have hmvt := norm_LFunction_sub_le_of_strip hχ (σ₁ := s.re) (σ₂ := 1) (t := t)
      (by linarith) hge1.le (by norm_num)
    have hlow := norm_LFunction_one_add_I_mul_ge hχ hcase
    have hs_eq : (s.re : ℂ) + I * (t : ℂ) = s := by
      have := Complex.re_add_im s
      simpa only [t, mul_comm I] using this
    have h1_eq : ((1 : ℝ) : ℂ) + I * (t : ℂ) = 1 + I * (t : ℂ) := by simp
    rw [hs_eq, h1_eq] at hmvt
    have hdiff_lt : (1 - s.re) * (288 * L ^ 2) < oneLineLowerConst / L ^ 7 := by
      have h1s : 1 - s.re ≤ zeroFreeConst / L ^ 9 := by linarith
      have hmul : (1 - s.re) * (288 * L ^ 2) ≤ (zeroFreeConst / L ^ 9) * (288 * L ^ 2) :=
        mul_le_mul_of_nonneg_right h1s (by positivity)
      have hhalf : (zeroFreeConst / L ^ 9) * (288 * L ^ 2) = (oneLineLowerConst / L ^ 7) / 2 := by
        unfold zeroFreeConst oneLineLowerConst
        field_simp [hL_pos.ne']
        ring
      have hpos_low : 0 < oneLineLowerConst / L ^ 7 :=
        div_pos oneLineLowerConst_pos (pow_pos hL_pos 7)
      linarith
    intro hzero
    rw [hzero, sub_zero] at hmvt
    linarith

/-- **UNCONDITIONAL CONCRETE ZERO-FREE REGION FOR PRIMITIVE NON-REAL DIRICHLET `L`-FUNCTIONS**
(0 assumptions, directly on Mathlib's `DirichletCharacter.LFunction`):
`∃ c > 0, ∀ q [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ^ 2 ≠ 1 → ∀ s : ℂ, 1 - c / (Real.log (q * (|s.im| + 2))) ^ 9 ≤ s.re → LFunction χ s ≠ 0`. -/
theorem LFunction_zeroFreeRegion_primitive_nonreal :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ^ 2 ≠ 1 →
        ∀ s : ℂ, 1 - c / (Real.log ((q : ℝ) * (|s.im| + 2))) ^ 9 ≤ s.re →
          LFunction χ s ≠ 0 := by
  refine ⟨zeroFreeConst, zeroFreeConst_pos, fun q _ χ _ hsq s hs => ?_⟩
  have hχ : χ ≠ 1 := fun h1 => hsq (by rw [h1, one_pow])
  exact LFunction_ne_zero_in_zeroFreeRegion hχ (Or.inl hsq) hs

/-- **UNCONDITIONAL CONCRETE ZERO-FREE REGION FOR ALL NON-PRINCIPAL DIRICHLET `L`-FUNCTIONS**
(`χ ^ 2 ≠ 1` OR `1 ≤ |s.im|`, 0 assumptions, directly on Mathlib's `DirichletCharacter.LFunction`). -/
theorem LFunction_zeroFreeRegion_unconditional :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ ≠ 1 →
        ∀ s : ℂ, (χ ^ 2 ≠ 1 ∨ 1 ≤ |s.im|) →
        1 - c / (Real.log ((q : ℝ) * (|s.im| + 2))) ^ 9 ≤ s.re →
          LFunction χ s ≠ 0 :=
  ⟨zeroFreeConst, zeroFreeConst_pos, fun _ _ _ hχ _ hcase hs =>
    LFunction_ne_zero_in_zeroFreeRegion hχ hcase hs⟩

end RHDirect.Stage5DirichletLZeroFree
