import RHDirect.Interfaces
import RHDirect.Stage3ZeroFreeRegion
import RHDirect.Stage5ZetaZeroFree
import RHDirect.Stage5DirichletLZeroFree
import RHDirect.Stage6ClassNumberFormula
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# RHDirect.Stage7SiegelWalfisz

100%-unconditional (`0` `sorry`, `0` custom `axiom`, `0` `HadamardLogDerivPackage` assumptions,
`0` warnings, `0` info) formalization directly on Mathlib's `DirichletCharacter.LFunction` in
pure Mathlib `v4.33.1`, establishing:

1. **Effective Dirichlet Lower Bounds on `L(1, χ)` (Section 1)**:
   - Integrality of real Dirichlet character values `charInt χ a ∈ {-1, 0, 1}` and exact integer
     representation of the odd class-number sum `∑_{a=1}^{q-1} a * (χ a).re`.
   - Unconditional `LFunction_one_ge_pi_div_q_sqrt_q`:
     `(LFunction χ 1).re ≥ π / (q * √q)` for EVERY odd real primitive character `χ mod q`.
   - Unit-annihilation congruence `((u : ZMod q) - charInt χ u) * S ≡ 0 (mod q)` and exact
     divisibility `(q : ℤ) ∣ ∑_{a=1}^{q-1} a * charInt χ a` for every odd real primitive `χ` of
     odd conductor `q ≥ 5`, yielding:
     - `LFunction_one_ge_pi_div_sqrt_q`: `(LFunction χ 1).re ≥ π / √q` for all odd `q ≥ 5`,
     - `LFunction_one_ge_pi_div_three_sqrt_q`: `(LFunction χ 1).re ≥ π / (3 * √q)` for ALL odd
       conductors `q` (including `q = 3`, where `L(1, χ₃) = π / (3 √3)` is sharp!).
   - Landau's quantitative `1 - β` ↔ `L(1, χ)` lower bound (`LFunction_one_le_mul_one_sub_zero`):
     for EVERY real non-principal `χ` (even or odd!) and EVERY real zero `β` of `LFunction χ`,
     `(LFunction χ 1).re ≤ (1 - β) * (288 * (Real.log (2 * q)) ^ 2)`.

2. **Unconditional Effective Real-Zero Exclusion for Odd Real Primitive `LFunction χ` (Section 2)**:
   - `LFunction_odd_real_primitive_zeroFree_real` (with explicit constant `1 / 100`):
     `1 - (1 / 100) / (q * √q * (log (2 * q)) ^ 2) ≤ β → LFunction χ β ≠ 0` for EVERY odd real
     primitive `χ mod q`.
   - `LFunction_odd_real_primitive_odd_cond_zeroFree_real` (with explicit constant `1 / 300`, and
     `1 / 100` for `q ≥ 5`):
     `1 - (1 / 300) / (√q * (log (2 * q)) ^ 2) ≤ β → LFunction χ β ≠ 0` for EVERY odd real
     primitive `χ` of odd conductor `q`.

3. **Unconditional Concrete Page–Landau Exceptional-Zero Isolation Directly on Mathlib's
   `DirichletCharacter.LFunction` (`0` Assumptions!, Section 3)**:
   - Unconditional single-character real-zero isolation (`LFunction_real_char_at_most_one_real_zero`):
     any real non-principal `χ mod q` has at most one real zero `β > 1 - 1 / (3000 * log (2 * q))`.
   - Unconditional two-distinct-characters Landau–Page theorem
     (`page_landau_two_distinct_nonprincipal_real_explicit`, explicit constant `1 / 3000`):
     via `Stage3ZeroFreeRegion.four_char_real_negLogDeriv_re_nonneg` and
     `Stage5ZetaZeroFree.landau_negLogDeriv_le_one_zero` / `landau_negLogDeriv_le`.
   - **Page's Full Uniform Theorem (`page_uniform_exceptional_zero_isolation` &
     `page_at_most_one_siegel_zero_unconditional`)**:
     `∃ c > 0`, for every `Q ≥ 2`, among ALL primitive Dirichlet characters `ψ` (real or complex!)
     of conductor `≤ Q`, there is AT MOST ONE `(ψ, β)` with `β : ℝ`, `LFunction ψ.χ β = 0`, and
     `1 - c / Real.log (2 * Q) < β` (and any such exceptional `ψ` is real and non-principal).
-/

noncomputable section

open Complex DirichletCharacter Finset RHDirect
open RHDirect.Stage3ZeroFreeRegion RHDirect.Stage5ZetaZeroFree
open RHDirect.Stage5DirichletLZeroFree RHDirect.Stage6ClassNumberFormula
open scoped BigOperators

namespace RHDirect.Stage7SiegelWalfisz

/-! ## Section 1: Integrality, Divisibility & Effective Lower Bounds on `L(1, χ)` -/

open Classical in
/-- Integer value `{-1, 0, 1}` associated to a Dirichlet character value `χ a`. -/
def charInt {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ZMod q) : ℤ :=
  if χ a = 1 then 1 else if χ a = -1 then -1 else 0

/-- Every value of a real Dirichlet character lies in `{0, 1, -1}`. -/
theorem real_char_apply_trichotomy {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (a : ZMod q) :
    χ a = 0 ∨ χ a = 1 ∨ χ a = -1 := by
  by_cases hu : IsUnit a
  · right
    have hsq : χ a * χ a = 1 := by
      have h1 : (χ ^ 2) a = (1 : DirichletCharacter ℂ q) a := by
        rw [isRealChar_sq_eq_one hreal]
      rw [sq, MulChar.mul_apply, MulChar.one_apply hu] at h1
      exact h1
    have hfac : (χ a - 1) * (χ a + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h1 | hm1
    · left; exact sub_eq_zero.mp h1
    · right; linear_combination hm1
  · left; exact MulChar.map_nonunit χ hu

/-- On units, every real Dirichlet character takes values in `{1, -1}`. -/
theorem real_char_unit_trichotomy {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (u : (ZMod q)ˣ) :
    χ (u : ZMod q) = 1 ∨ χ (u : ZMod q) = -1 := by
  have hsq : χ (u : ZMod q) * χ (u : ZMod q) = 1 := by
    have h1 : (χ ^ 2) (u : ZMod q) = (1 : DirichletCharacter ℂ q) (u : ZMod q) := by
      rw [isRealChar_sq_eq_one hreal]
    rw [sq, MulChar.mul_apply, MulChar.one_apply u.isUnit] at h1
    exact h1
  have hfac : (χ (u : ZMod q) - 1) * (χ (u : ZMod q) + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h1 | hm1
  · left; exact sub_eq_zero.mp h1
  · right; linear_combination hm1

/-- Exact cast identity `((charInt χ a : ℤ) : ℂ) = χ a` for every real Dirichlet character `χ`. -/
theorem charInt_cast_complex {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (a : ZMod q) :
    ((charInt χ a : ℤ) : ℂ) = χ a := by
  classical
  unfold charInt
  rcases real_char_apply_trichotomy hreal a with h0 | h1 | hm1
  · rw [if_neg (by rw [h0]; norm_num), if_neg (by rw [h0]; norm_num), h0]; simp
  · rw [if_pos h1, h1]; simp
  · rw [if_neg (by rw [hm1]; norm_num), if_pos hm1, hm1]; simp

/-- Exact cast identity `((charInt χ a : ℤ) : ℝ) = (χ a).re` for every real Dirichlet character `χ`. -/
theorem charInt_cast_real {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (a : ZMod q) :
    ((charInt χ a : ℤ) : ℝ) = (χ a).re := by
  have h := congrArg Complex.re (charInt_cast_complex hreal a)
  simpa using h

/-- Multiplicativity of `charInt χ` for every real Dirichlet character `χ`. -/
theorem charInt_mul {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (a b : ZMod q) :
    charInt χ (a * b) = charInt χ a * charInt χ b := by
  have hC : ((charInt χ (a * b) : ℤ) : ℂ) = (((charInt χ a * charInt χ b : ℤ) : ℂ)) := by
    rw [Int.cast_mul, charInt_cast_complex hreal, charInt_cast_complex hreal,
      charInt_cast_complex hreal, map_mul]
  exact Int.cast_injective hC

/-- For a real Dirichlet character, `charInt χ u⁻¹ = charInt χ u` on units. -/
theorem charInt_inv_unit {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (u : (ZMod q)ˣ) :
    charInt χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = charInt χ (u : ZMod q) := by
  have hC : ((charInt χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) : ℤ) : ℂ) =
      ((charInt χ (u : ZMod q) : ℤ) : ℂ) := by
    rw [charInt_cast_complex hreal, charInt_cast_complex hreal]
    rcases real_char_unit_trichotomy hreal u with h1 | hm1
    · have hmul : χ (u : ZMod q) * χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [h1, one_mul] at hmul; rw [hmul, h1]
    · have hmul : χ (u : ZMod q) * χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [hm1] at hmul
      linear_combination -hmul + hm1.symm
  exact Int.cast_injective hC

/-- Every odd character is non-principal (`χ ≠ 1`). -/
theorem ne_one_of_odd {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hodd : χ.Odd) :
    χ ≠ 1 := by
  intro h1
  have h2 : χ (-1 : ZMod q) = 1 := by rw [h1]; exact MulChar.one_apply isUnit_one.neg
  have h3 : χ (-1 : ZMod q) = -1 := hodd
  rw [h2] at h3
  norm_num at h3

/-- Exact integer representation of `∑_{a=1}^{q-1} a * (χ a).re`. -/
theorem sum_mul_re_eq_intCast {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    ∑ a ∈ Finset.Ico 1 q, (a : ℝ) * (χ (a : ZMod q)).re =
      ((∑ a ∈ Finset.Ico 1 q, (a : ℤ) * charInt χ (a : ZMod q) : ℤ) : ℝ) := by
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Int.cast_mul, Int.cast_natCast, charInt_cast_real hreal]

/-- For every odd real primitive character `χ mod q`, the integer sum
`∑_{a=1}^{q-1} a * charInt χ a` is strictly negative (hence `≤ -1`). -/
theorem sum_mul_odd_real_primitive_le_neg_one {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hodd : χ.Odd)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    ∑ a ∈ Finset.Ico 1 q, (a : ℤ) * charInt χ (a : ZMod q) ≤ -1 := by
  have hneg : ∑ a ∈ Finset.Ico 1 q, (a : ℝ) * (χ (a : ZMod q)).re < 0 :=
    dirichlet_sign_theorem_odd_real_primitive hprim hodd hreal
  rw [sum_mul_re_eq_intCast hreal] at hneg
  have hlt : ∑ a ∈ Finset.Ico 1 q, (a : ℤ) * charInt χ (a : ZMod q) < 0 :=
    Int.cast_lt (R := ℝ).mp (by simpa using hneg)
  omega

/-- **UNCONDITIONAL EFFECTIVE DIRICHLET LOWER BOUND (`π / (q √q)`)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY odd real primitive character `χ : DirichletCharacter ℂ q`:
`(DirichletCharacter.LFunction χ 1).re ≥ π / (q * √q)`. -/
theorem LFunction_one_ge_pi_div_q_sqrt_q {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hodd : χ.Odd)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    Real.pi / ((q : ℝ) * Real.sqrt (q : ℝ)) ≤ (DirichletCharacter.LFunction χ 1).re := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hcoeff_pos : 0 < Real.pi / ((q : ℝ) * Real.sqrt (q : ℝ)) :=
    div_pos Real.pi_pos (mul_pos hq_pos (Real.sqrt_pos.mpr hq_pos))
  have hsum_le : ∑ a ∈ Finset.Ico 1 q, (a : ℝ) * (χ (a : ZMod q)).re ≤ -1 := by
    rw [sum_mul_re_eq_intCast hreal]
    exact_mod_cast sum_mul_odd_real_primitive_le_neg_one hprim hodd hreal
  rw [re_LFunction_one_eq_odd_real_primitive hprim hodd hreal]
  nlinarith

/-- **Unit-Annihilation Congruence in `ZMod q`**:
for every real character `χ mod q` and every unit `u : (ZMod q)ˣ`,
`((u : ZMod q) - (charInt χ u : ZMod q)) * (∑_{a=1}^{q-1} a * charInt χ a : ZMod q) = 0`. -/
theorem unit_sub_charInt_mul_sum_eq_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hreal : ∀ a : ZMod q, (χ a).im = 0) (u : (ZMod q)ˣ) :
    ((u : ZMod q) - (charInt χ (u : ZMod q) : ZMod q)) *
        ((∑ a ∈ Finset.Ico 1 q, (a : ℤ) * charInt χ (a : ZMod q) : ℤ) : ZMod q) = 0 := by
  set S : ZMod q := ((∑ a ∈ Finset.Ico 1 q, (a : ℤ) * charInt χ (a : ZMod q) : ℤ) : ZMod q)
  have hS_eq : S = ∑ x : ZMod q, x * (charInt χ x : ZMod q) := by
    dsimp only [S]
    rw [Int.cast_sum]
    have hrange :
        ∑ a ∈ Finset.Ico 1 q, (((a : ℤ) * charInt χ (a : ZMod q) : ℤ) : ZMod q) =
          ∑ a ∈ Finset.range q, (a : ZMod q) * (charInt χ (a : ZMod q) : ZMod q) := by
      have hsp : Finset.range q = insert 0 (Finset.Ico 1 q) := by
        ext a; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
        have hq0 : 0 < q := NeZero.pos q
        omega
      rw [hsp, Finset.sum_insert (by simp)]
      simp only [Nat.cast_zero, zero_mul, zero_add]
      refine Finset.sum_congr rfl fun a _ => by push_cast; rfl
    rw [hrange]
    refine Finset.sum_bij (fun a _ => (a : ZMod q)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro a₁ ha₁ a₂ ha₂ h
      simp only [Finset.mem_range] at ha₁ ha₂
      have hv := congrArg ZMod.val h
      rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha₁, Nat.mod_eq_of_lt ha₂] at hv
    · intro x _
      exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
    · intro _ _; rfl
  have hmul : (u : ZMod q) * S = (charInt χ (u : ZMod q) : ZMod q) * S := by
    rw [hS_eq, Finset.mul_sum, Finset.mul_sum]
    calc ∑ x : ZMod q, (u : ZMod q) * (x * (charInt χ x : ZMod q))
        = ∑ x : ZMod q, ((u : ZMod q) * x) * (charInt χ x : ZMod q) :=
          Finset.sum_congr rfl fun x _ => by ring
      _ = ∑ y : ZMod q, y * (charInt χ (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * y) : ZMod q) :=
          Fintype.sum_equiv (MulAction.toPerm u) _ _ fun x => by
            show ((u : ZMod q) * x) * (charInt χ x : ZMod q) =
              ((u : ZMod q) * x) *
                (charInt χ (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ((u : ZMod q) * x)) : ZMod q)
            rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = ∑ y : ZMod q, (charInt χ (u : ZMod q) : ZMod q) * (y * (charInt χ y : ZMod q)) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [charInt_mul hreal, charInt_inv_unit hreal u, Int.cast_mul]
          ring
  linear_combination hmul

/-- **Exact Conductor Divisibility for Odd Real Primitive Characters of Odd Conductor `q ≥ 5`**:
`(q : ℤ) ∣ ∑_{a=1}^{q-1} a * charInt χ a`.
(Note: for `q = 3`, the sum equals `-1` and `L(1, χ₃) = π / (3 √3)`, so `q ≥ 5` is sharp!) -/
theorem dvd_sum_mul_odd_real_primitive {q : ℕ} [NeZero q] (hq_odd : Odd q) (hq5 : 5 ≤ q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    (q : ℤ) ∣ ∑ a ∈ Finset.Ico 1 q, (a : ℤ) * charInt χ (a : ZMod q) := by
  set S_int : ℤ := ∑ a ∈ Finset.Ico 1 q, (a : ℤ) * charInt χ (a : ZMod q)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2cop : Nat.Coprime 2 q := by
    obtain ⟨t, ht⟩ := hq_odd
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr (by omega)
  have h2u : IsUnit (2 : ZMod q) := (ZMod.isUnit_iff_coprime 2 q).mpr h2cop
  have h2ann := unit_sub_charInt_mul_sum_eq_zero hreal h2u.unit
  have h2val : (h2u.unit : ZMod q) = (2 : ZMod q) := h2u.unit_spec
  rw [h2val] at h2ann
  rcases real_char_unit_trichotomy hreal h2u.unit with hχ2 | hχ2
  · -- `χ(2) = 1` ⇒ `(2 - 1) * S = 0` ⇒ `S = 0` in `ZMod q`!
    rw [h2val] at hχ2
    have hci : charInt χ (2 : ZMod q) = 1 := by
      classical
      unfold charInt
      rw [if_pos hχ2]
    rw [hci] at h2ann
    have h21 : (2 : ZMod q) - ((1 : ℤ) : ZMod q) = 1 := by push_cast; ring
    rw [h21, one_mul] at h2ann
    exact h2ann
  · -- `χ(2) = -1` ⇒ `3 * S = 0` in `ZMod q`
    rw [h2val] at hχ2
    have hci : charInt χ (2 : ZMod q) = -1 := by
      classical
      unfold charInt
      rw [if_neg (by rw [hχ2]; norm_num), if_pos hχ2]
    rw [hci] at h2ann
    have h3S : (3 : ZMod q) * (S_int : ZMod q) = 0 := by
      have h21 : (2 : ZMod q) - ((-1 : ℤ) : ZMod q) = (3 : ZMod q) := by push_cast; ring
      rwa [h21] at h2ann
    by_cases h3dvd : 3 ∣ q
    · -- `3 ∣ q` and `q ≥ 5`: since `χ` is primitive of conductor `q`, `¬ χ.FactorsThrough 3`!
      have hnfac : ¬ χ.FactorsThrough 3 := by
        intro hfac
        have hdvd : χ.conductor ∣ 3 :=
          (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ h3dvd).mp hfac
        rw [hprim] at hdvd
        have hle := Nat.le_of_dvd (by norm_num) hdvd
        omega
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap h3dvd] at hnfac
      have hex : ∃ u : (ZMod q)ˣ, u ∈ MonoidHom.ker (ZMod.unitsMap h3dvd) ∧ χ (u : ZMod q) ≠ 1 := by
        by_contra hall
        push Not at hall
        apply hnfac
        intro u hu
        rw [MonoidHom.mem_ker]
        apply Units.ext
        simpa [MulChar.coe_toUnitHom] using hall u hu
      obtain ⟨u, hu_ker, hu_ne1⟩ := hex
      have hχu : χ (u : ZMod q) = -1 := (real_char_unit_trichotomy hreal u).resolve_left hu_ne1
      have hciu : charInt χ (u : ZMod q) = -1 := by
        classical
        unfold charInt
        rw [if_neg (by rw [hχu]; norm_num), if_pos hχu]
      have hu_ann := unit_sub_charInt_mul_sum_eq_zero hreal u
      rw [hciu] at hu_ann
      -- `u ≡ 1 (mod 3)`, so `(u.val + 1) % 3 = 2`, giving explicit Bézout identity with `3`!
      have hu_mod3 : (u : ZMod q).val % 3 = 1 := by
        rw [MonoidHom.mem_ker] at hu_ker
        have hv : ZMod.cast (u : ZMod q) = (1 : ZMod 3) := by
          have := congrArg Units.val hu_ker
          simpa [ZMod.unitsMap_def] using this
        rw [ZMod.cast_eq_val] at hv
        have hm := (ZMod.natCast_eq_natCast_iff (u : ZMod q).val 1 3).mp (by simpa using hv)
        simpa [Nat.ModEq] using hm
      set k : ℕ := (u : ZMod q).val + 1
      have hk_cast : (k : ZMod q) = (u : ZMod q) - ((-1 : ℤ) : ZMod q) := by
        dsimp only [k]
        push_cast
        rw [ZMod.natCast_zmod_val]
        ring
      have hkS : (k : ZMod q) * (S_int : ZMod q) = 0 := by rwa [hk_cast]
      set m : ℕ := k / 3
      have hk_eq : k = 3 * m + 2 := by omega
      have hbez : (2 : ZMod q) * (k : ZMod q) - ((2 * m + 1 : ℕ) : ZMod q) * (3 : ZMod q) = 1 := by
        have hZ : (2 : ℤ) * (k : ℤ) - ((2 * m + 1 : ℕ) : ℤ) * 3 = 1 := by omega
        have hcast := congrArg (Int.cast : ℤ → ZMod q) hZ
        simpa using hcast
      calc (S_int : ZMod q)
          = 1 * (S_int : ZMod q) := (one_mul _).symm
        _ = ((2 : ZMod q) * (k : ZMod q) - ((2 * m + 1 : ℕ) : ZMod q) * (3 : ZMod q)) *
              (S_int : ZMod q) := by rw [hbez]
        _ = (2 : ZMod q) * ((k : ZMod q) * (S_int : ZMod q)) -
              ((2 * m + 1 : ℕ) : ZMod q) * ((3 : ZMod q) * (S_int : ZMod q)) := by ring
        _ = 0 := by rw [hkS, h3S]; ring
    · -- `¬ 3 ∣ q` ⇒ `3` is a unit in `ZMod q` ⇒ `S = 0`!
      have h3cop : Nat.Coprime 3 q :=
        (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mpr h3dvd
      have h3u : IsUnit (3 : ZMod q) := (ZMod.isUnit_iff_coprime 3 q).mpr h3cop
      obtain ⟨u3, hu3⟩ := h3u
      have hmul := congrArg (((u3⁻¹ : (ZMod q)ˣ) : ZMod q) * ·) h3S
      rw [← mul_assoc, ← hu3, Units.inv_mul, one_mul, mul_zero] at hmul
      exact hmul

/-- **UNCONDITIONAL SHARP DIRICHLET LOWER BOUND (`π / √q`) FOR ODD CONDUCTORS `q ≥ 5`**:
for every odd real primitive character `χ : DirichletCharacter ℂ q` with `Odd q` and `5 ≤ q`:
`(DirichletCharacter.LFunction χ 1).re ≥ π / √q`. -/
theorem LFunction_one_ge_pi_div_sqrt_q {q : ℕ} [NeZero q] (hq_odd : Odd q) (hq5 : 5 ≤ q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hodd : χ.Odd)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    Real.pi / Real.sqrt (q : ℝ) ≤ (DirichletCharacter.LFunction χ 1).re := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hsqrt_pos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq_pos
  have hdvd := dvd_sum_mul_odd_real_primitive hq_odd hq5 hprim hreal
  have hneg := sum_mul_odd_real_primitive_le_neg_one hprim hodd hreal
  obtain ⟨k, hk⟩ := hdvd
  have hk_neg : k ≤ -1 := by
    have hqZ : (0 : ℤ) < (q : ℤ) := Int.natCast_pos.mpr (NeZero.pos q)
    nlinarith
  have hS_le : ∑ a ∈ Finset.Ico 1 q, (a : ℤ) * charInt χ (a : ZMod q) ≤ -(q : ℤ) := by
    rw [hk]
    have hqZ : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
    nlinarith
  have hS_real : ∑ a ∈ Finset.Ico 1 q, (a : ℝ) * (χ (a : ZMod q)).re ≤ -(q : ℝ) := by
    rw [sum_mul_re_eq_intCast hreal]
    exact_mod_cast hS_le
  rw [re_LFunction_one_eq_odd_real_primitive hprim hodd hreal]
  have hcoeff_pos : 0 < Real.pi / ((q : ℝ) * Real.sqrt (q : ℝ)) :=
    div_pos Real.pi_pos (mul_pos hq_pos hsqrt_pos)
  have hid : -(Real.pi / ((q : ℝ) * Real.sqrt (q : ℝ))) * -(q : ℝ) =
      Real.pi / Real.sqrt (q : ℝ) := by
    field_simp [hq_pos.ne', hsqrt_pos.ne']
  nlinarith

/-- **UNCONDITIONAL `π / (3 √q)` LOWER BOUND FOR ALL ODD CONDUCTORS `q` (INCLUDING `q = 3`!)**:
for EVERY odd conductor `q` and EVERY odd real primitive `χ : DirichletCharacter ℂ q`:
`(DirichletCharacter.LFunction χ 1).re ≥ π / (3 * √q)`. -/
theorem LFunction_one_ge_pi_div_three_sqrt_q {q : ℕ} [NeZero q] (hq_odd : Odd q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hodd : χ.Odd)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    Real.pi / (3 * Real.sqrt (q : ℝ)) ≤ (DirichletCharacter.LFunction χ 1).re := by
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one (ne_one_of_odd hodd)
  obtain ⟨t, ht⟩ := hq_odd
  by_cases hq5 : 5 ≤ q
  · have h := LFunction_one_ge_pi_div_sqrt_q ⟨t, ht⟩ hq5 hprim hodd hreal
    have hsqrt_pos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos q))
    have hle : Real.pi / (3 * Real.sqrt (q : ℝ)) ≤ Real.pi / Real.sqrt (q : ℝ) := by
      apply div_le_div_of_nonneg_left Real.pi_pos.le hsqrt_pos
      linarith
    exact hle.trans h
  · have hq3 : q = 3 := by omega
    have h := LFunction_one_ge_pi_div_q_sqrt_q hprim hodd hreal
    simpa [hq3] using h

/-- **Landau's Quantitative `1 - β` ↔ `L(1, χ)` Lower Bound (General Non-Principal `χ`,
Even OR Odd!)**:
for EVERY non-principal `χ : DirichletCharacter ℂ q` (`χ ≠ 1`) and EVERY
real zero `β : ℝ` of `DirichletCharacter.LFunction χ`:
`(DirichletCharacter.LFunction χ 1).re ≤ (1 - β) * (288 * (Real.log (2 * q)) ^ 2)`. -/
theorem LFunction_one_le_mul_one_sub_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {β : ℝ} (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    (DirichletCharacter.LFunction χ 1).re ≤
      (1 - β) * (288 * (Real.log (2 * (q : ℝ))) ^ 2) := by
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hlog4 : (1.38 : ℝ) < Real.log 4 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_gt_d9]
  set L : ℝ := Real.log (2 * (q : ℝ))
  have hL : (1.38 : ℝ) < L := lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) (by linarith))
  have hL_pos : 0 < L := by linarith
  have hβ_lt1 : β < 1 := by
    by_contra hge; push Not at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simpa using hge) hzero
  have harg : (q : ℝ) * (|(0 : ℝ)| + 2) = 2 * (q : ℝ) := by simp [mul_comm]
  by_cases hnear : 1 - L⁻¹ ≤ β
  · have hmvt := norm_LFunction_sub_le_of_strip hχ (σ₁ := β) (σ₂ := 1) (t := 0)
      (by rw [harg]; exact hnear) hβ_lt1.le (by norm_num)
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_zero, add_zero, harg] at hmvt
    rw [hzero, sub_zero] at hmvt
    have hre_le : (DirichletCharacter.LFunction χ 1).re ≤ ‖DirichletCharacter.LFunction χ 1‖ :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
    exact hre_le.trans hmvt
  · push Not at hnear
    have hup := norm_LFunction_le_log_of_one_le_re hχ (s := 1) (by simp) (by simp)
    simp only [Complex.one_im, harg] at hup
    have hre_le : (DirichletCharacter.LFunction χ 1).re ≤ 5 * L :=
      ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans hup
    have h1β : L⁻¹ < 1 - β := by linarith
    have hmul : 288 * L < (1 - β) * (288 * L ^ 2) := by
      have h1 : L⁻¹ * (288 * L ^ 2) = 288 * L := by field_simp [hL_pos.ne']
      rw [← h1]
      exact mul_lt_mul_of_pos_right h1β (by positivity)
    linarith

/-- Quotient form of Landau's `1 - β` ↔ `L(1, χ)` quantitative lower bound. -/
theorem one_sub_zero_ge_LFunction_one_div {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {β : ℝ} (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    (DirichletCharacter.LFunction χ 1).re / (288 * (Real.log (2 * (q : ℝ))) ^ 2) ≤ 1 - β := by
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hL_pos : 0 < Real.log (2 * (q : ℝ)) :=
    Real.log_pos (by linarith)
  rw [div_le_iff₀ (by positivity)]
  exact LFunction_one_le_mul_one_sub_zero hχ hzero

/-! ## Section 2: Unconditional Effective Real-Zero Exclusion for Odd Real Primitive Characters -/

/-- **UNCONDITIONAL EFFECTIVE REAL-ZERO EXCLUSION (EXPLICIT CONSTANT `1 / 100`)**:
for EVERY `q ≥ 1` (`[NeZero q]`), EVERY odd real primitive `χ : DirichletCharacter ℂ q`,
and EVERY `β : ℝ`:
`1 - (1 / 100) / (q * √q * (log (2 * q)) ^ 2) ≤ β → DirichletCharacter.LFunction χ β ≠ 0`. -/
theorem LFunction_odd_real_primitive_ne_zero_real_explicit {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    (hodd : χ.Odd) {β : ℝ}
    (hβ : 1 - (1 / 100 : ℝ) / ((q : ℝ) * Real.sqrt (q : ℝ) * (Real.log (2 * (q : ℝ))) ^ 2) ≤ β) :
    DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  intro hzero
  have hχ : χ ≠ 1 := ne_one_of_odd hodd
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsqrt_pos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq_pos
  set L : ℝ := Real.log (2 * (q : ℝ))
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * q))
  have hlow := LFunction_one_ge_pi_div_q_sqrt_q hprim hodd hreal
  have hup : (DirichletCharacter.LFunction χ 1).re ≤ (1 - β) * (288 * L ^ 2) :=
    LFunction_one_le_mul_one_sub_zero hχ hzero
  have h1β : 1 - β ≤ (1 / 100 : ℝ) / ((q : ℝ) * Real.sqrt (q : ℝ) * L ^ 2) := by
    linarith
  have hmul :
      (1 - β) * (288 * L ^ 2) ≤ (288 / 100 : ℝ) / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
    calc (1 - β) * (288 * L ^ 2)
        ≤ ((1 / 100 : ℝ) / ((q : ℝ) * Real.sqrt (q : ℝ) * L ^ 2)) * (288 * L ^ 2) :=
          mul_le_mul_of_nonneg_right h1β (by positivity)
      _ = (288 / 100 : ℝ) / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
          field_simp [hq_pos.ne', hsqrt_pos.ne', hL_pos.ne']
  have hpi : (288 / 100 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have hlt : (288 / 100 : ℝ) / ((q : ℝ) * Real.sqrt (q : ℝ)) <
      Real.pi / ((q : ℝ) * Real.sqrt (q : ℝ)) :=
    div_lt_div_of_pos_right hpi (mul_pos hq_pos hsqrt_pos)
  linarith

/-- **UNCONDITIONAL EFFECTIVE REAL-ZERO EXCLUSION FOR ALL ODD REAL PRIMITIVE `LFunction χ`**
(`0` assumptions!):
`∃ c > 0, ∀ q [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → (∀ a, (χ a).im = 0) →
  χ.Odd → ∀ β : ℝ, 1 - c / (q * √q * (log (2 * q)) ^ 2) ≤ β → LFunction χ β ≠ 0`. -/
theorem LFunction_odd_real_primitive_zeroFree_real :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → (∀ a, (χ a).im = 0) → χ.Odd →
        ∀ β : ℝ,
          1 - c / ((q : ℝ) * Real.sqrt (q : ℝ) * (Real.log (2 * (q : ℝ))) ^ 2) ≤ β →
          DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 :=
  ⟨1 / 100, by norm_num, fun _ _ _ hprim hreal hodd _ hβ =>
    LFunction_odd_real_primitive_ne_zero_real_explicit hprim hreal hodd hβ⟩

/-- **SHARPER UNCONDITIONAL EFFECTIVE REAL-ZERO EXCLUSION FOR ALL ODD CONDUCTORS `q`**
(explicit constant `1 / 300`, covering every odd `q` including `q = 3`!):
`1 - (1 / 300) / (√q * (log (2 * q)) ^ 2) ≤ β → DirichletCharacter.LFunction χ β ≠ 0`. -/
theorem LFunction_odd_real_primitive_odd_cond_ne_zero_real_explicit {q : ℕ} [NeZero q]
    (hq_odd : Odd q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0) (hodd : χ.Odd) {β : ℝ}
    (hβ : 1 - (1 / 300 : ℝ) / (Real.sqrt (q : ℝ) * (Real.log (2 * (q : ℝ))) ^ 2) ≤ β) :
    DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  intro hzero
  have hχ : χ ≠ 1 := ne_one_of_odd hodd
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsqrt_pos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq_pos
  set L : ℝ := Real.log (2 * (q : ℝ))
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * q))
  have hlow := LFunction_one_ge_pi_div_three_sqrt_q hq_odd hprim hodd hreal
  have hup : (DirichletCharacter.LFunction χ 1).re ≤ (1 - β) * (288 * L ^ 2) :=
    LFunction_one_le_mul_one_sub_zero hχ hzero
  have h1β : 1 - β ≤ (1 / 300 : ℝ) / (Real.sqrt (q : ℝ) * L ^ 2) := by
    linarith
  have hmul :
      (1 - β) * (288 * L ^ 2) ≤ (288 / 100 : ℝ) / (3 * Real.sqrt (q : ℝ)) := by
    calc (1 - β) * (288 * L ^ 2)
        ≤ ((1 / 300 : ℝ) / (Real.sqrt (q : ℝ) * L ^ 2)) * (288 * L ^ 2) :=
          mul_le_mul_of_nonneg_right h1β (by positivity)
      _ = (288 / 100 : ℝ) / (3 * Real.sqrt (q : ℝ)) := by
          field_simp [hsqrt_pos.ne', hL_pos.ne']
          ring
  have hpi : (288 / 100 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have hlt : (288 / 100 : ℝ) / (3 * Real.sqrt (q : ℝ)) <
      Real.pi / (3 * Real.sqrt (q : ℝ)) :=
    div_lt_div_of_pos_right hpi (by positivity)
  linarith

/-- **SHARPER UNCONDITIONAL EFFECTIVE REAL-ZERO EXCLUSION FOR ALL ODD CONDUCTORS `q`**
(`0` assumptions!):
`∃ c > 0, ∀ q [NeZero q], Odd q → ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
  (∀ a, (χ a).im = 0) → χ.Odd → ∀ β : ℝ,
  1 - c / (√q * (log (2 * q)) ^ 2) ≤ β → LFunction χ β ≠ 0`. -/
theorem LFunction_odd_real_primitive_odd_cond_zeroFree_real :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], Odd q →
        ∀ (χ : DirichletCharacter ℂ q),
          χ.IsPrimitive → (∀ a, (χ a).im = 0) → χ.Odd →
          ∀ β : ℝ,
            1 - c / (Real.sqrt (q : ℝ) * (Real.log (2 * (q : ℝ))) ^ 2) ≤ β →
            DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 :=
  ⟨1 / 300, by norm_num, fun _ _ hq_odd _ hprim hreal hodd _ hβ =>
    LFunction_odd_real_primitive_odd_cond_ne_zero_real_explicit hq_odd hprim hreal hodd hβ⟩

/-! ## Section 3: Unconditional Concrete Page–Landau Exceptional-Zero Isolation (`0` Assumptions!) -/

/-- Helper: `L(χ, ·)` analyticity, nonvanishing, ratio bound `M = 12 * B / δ`, and zero-re bound
on `closedBall (σ : ℂ) (1 / 2)` for any non-principal `χ ≠ 1` mod `q` with `(q : ℝ) ≤ B`,
`1 < σ ≤ 5 / 4`, `σ - 1 = δ`. -/
private lemma LFunction_landau_setup_real {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {B δ : ℝ} (hB : (q : ℝ) ≤ B) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    let σ : ℝ := 1 + δ
    let M : ℝ := 12 * B / δ
    1 ≤ M ∧
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall (σ : ℂ) (1 / 2)) ∧
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 ∧
    (∀ z ∈ Metric.closedBall (σ : ℂ) (1 / 2),
      ‖DirichletCharacter.LFunction χ z‖ ≤ M * ‖DirichletCharacter.LFunction χ (σ : ℂ)‖) ∧
    (∀ ρ ∈ Metric.closedBall (σ : ℂ) (1 / 4),
      DirichletCharacter.LFunction χ ρ = 0 → ρ.re ≤ (σ : ℂ).re) := by
  intro σ M
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hB1 : 1 ≤ B := hq1.trans hB
  have hσ1 : 1 < σ := by dsimp only [σ]; linarith
  have hσ2 : σ ≤ 5 / 4 := by dsimp only [σ]; linarith
  have hM_ge1 : 1 ≤ M := by
    dsimp only [M]
    rw [le_div_iff₀ hδ0]
    linarith
  have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall (σ : ℂ) (1 / 2)) :=
    (DifferentiableOn.analyticOnNhd
      (fun z _ => (DirichletCharacter.differentiableAt_LFunction χ z (.inr hχ)).differentiableWithinAt)
      isOpen_univ).mono (Set.subset_univ _)
  have hnz : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simp [hσ1.le])
  have hbd : ∀ z ∈ Metric.closedBall (σ : ℂ) (1 / 2),
      ‖DirichletCharacter.LFunction χ z‖ ≤ M * ‖DirichletCharacter.LFunction χ (σ : ℂ)‖ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - (σ : ℂ))).trans hz)
    have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - (σ : ℂ))).trans hz)
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
      sub_zero] at hre_diff him_diff
    have hz_strip : ‖DirichletCharacter.LFunction χ z‖ ≤ 6 * B := by
      have h := norm_LFunction_strip_le hχ (by linarith : 1 / 2 ≤ z.re) (by linarith : z.re ≤ 2)
      have him_abs : |z.im| ≤ 1 / 2 := abs_le.mpr him_diff
      have hq_nn : (0 : ℝ) ≤ (q : ℝ) := by linarith
      nlinarith
    have hinv : ‖1 / DirichletCharacter.LFunction χ (σ : ℂ)‖ ≤ 2 / δ := by
      have h := (norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ hσ1 0).2.1
      simp only [Complex.ofReal_zero, mul_zero, add_zero] at h
      have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
      rw [hσ_sub] at h
      exact h.trans (div_le_div_of_nonneg_right (by linarith) hδ0.le)
    have h1 : ‖DirichletCharacter.LFunction χ z‖ / ‖DirichletCharacter.LFunction χ (σ : ℂ)‖ ≤ M := by
      rw [← norm_div, show DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ (σ : ℂ) =
          DirichletCharacter.LFunction χ z * (1 / DirichletCharacter.LFunction χ (σ : ℂ)) by ring,
        norm_mul]
      calc ‖DirichletCharacter.LFunction χ z‖ * ‖1 / DirichletCharacter.LFunction χ (σ : ℂ)‖
          ≤ (6 * B) * (2 / δ) := mul_le_mul hz_strip hinv (norm_nonneg _) (by positivity)
        _ = M := by dsimp only [M]; ring
    exact (div_le_iff₀ (norm_pos_iff.mpr hnz)).mp h1
  have hzeros : ∀ ρ ∈ Metric.closedBall (σ : ℂ) (1 / 4),
      DirichletCharacter.LFunction χ ρ = 0 → ρ.re ≤ (σ : ℂ).re := by
    intro ρ _ hρ0
    by_contra hgt; push Not at hgt
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ)
      (by simp only [Complex.ofReal_re] at hgt; linarith) hρ0
  exact ⟨hM_ge1, han, hnz, hbd, hzeros⟩

/-- **UNCONDITIONAL SINGLE-CHARACTER REAL-ZERO ISOLATION (`0` ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`), EVERY non-principal `χ : DirichletCharacter ℂ q` (`χ ≠ 1`),
and ANY two distinct real zeros `β₁ ≠ β₂` of `DirichletCharacter.LFunction χ`:
`min β₁ β₂ ≤ 1 - 1 / (3000 * Real.log (2 * q))`. -/
theorem LFunction_real_char_at_most_one_real_zero_unconditional {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {β₁ β₂ : ℝ} (hne : β₁ ≠ β₂)
    (hz1 : DirichletCharacter.LFunction χ (β₁ : ℂ) = 0)
    (hz2 : DirichletCharacter.LFunction χ (β₂ : ℂ) = 0) :
    min β₁ β₂ ≤ 1 - 1 / (3000 * Real.log (2 * (q : ℝ))) := by
  by_contra hgt; push Not at hgt
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hlog4 : (1.38 : ℝ) < Real.log 4 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_gt_d9]
  set L : ℝ := Real.log (2 * (q : ℝ))
  have hL : (1.38 : ℝ) < L := lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) (by linarith))
  have hL_pos : 0 < L := by linarith
  set δ : ℝ := 1 / (600 * L)
  have hδ0 : 0 < δ := by positivity
  have hδ_le : δ ≤ 1 / 4 := by
    dsimp only [δ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set σ : ℝ := 1 + δ
  have hσ1 : 1 < σ := by linarith
  have hβ1_lt1 : β₁ < 1 := by
    by_contra h; push Not at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simpa using h) hz1
  have hβ2_lt1 : β₂ < 1 := by
    by_contra h; push Not at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simpa using h) hz2
  set β : ℝ := min β₁ β₂
  have hβ_gt : 1 - δ / 5 < β := by
    have hδ5 : δ / 5 = 1 / (3000 * L) := by dsimp only [δ]; field_simp [hL_pos.ne']; ring
    linarith
  have hβ1_mem : (β₁ : ℂ) ∈ Metric.closedBall (σ : ℂ) (1 / 4) := by
    rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith)]
    have h1 : β ≤ β₁ := min_le_left β₁ β₂
    have hδ_small : δ < 1 / 600 := by
      dsimp only [δ]; rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
    dsimp only [σ]; linarith
  have hβ2_mem : (β₂ : ℂ) ∈ Metric.closedBall (σ : ℂ) (1 / 4) := by
    rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith)]
    have h2 : β ≤ β₂ := min_le_right β₁ β₂
    have hδ_small : δ < 1 / 600 := by
      dsimp only [δ]; rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
    dsimp only [σ]; linarith
  obtain ⟨hM_ge1, han, hnz, hbd, hzeros⟩ :=
    LFunction_landau_setup_real hχ (B := (q : ℝ)) le_rfl hδ0 hδ_le
  set M : ℝ := 12 * (q : ℝ) / δ
  set S : Finset ℂ := {(β₁ : ℂ), (β₂ : ℂ)}
  have hneC : (β₁ : ℂ) ≠ (β₂ : ℂ) := fun h => hne (Complex.ofReal_injective h)
  have hS : ∀ ρ ∈ S, ρ ∈ Metric.closedBall (σ : ℂ) (1 / 4) ∧ DirichletCharacter.LFunction χ ρ = 0 := by
    intro ρ hρ
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hρ
    rcases hρ with rfl | rfl
    · exact ⟨hβ1_mem, hz1⟩
    · exact ⟨hβ2_mem, hz2⟩
  have hhalf : (1 / 2 : ℝ) / 2 = 1 / 4 := by norm_num
  have hlandau := landau_negLogDeriv_le_finset_zeros (R := 1 / 2) (M := M) (by norm_num) hM_ge1
    han hnz hbd (by rw [hhalf]; exact hzeros) S (by rw [hhalf]; exact hS)
  have hsum_S : ∑ ρ ∈ S, (1 / ((σ : ℂ) - ρ)).re = 1 / (σ - β₁) + 1 / (σ - β₂) := by
    dsimp only [S]
    rw [Finset.sum_pair hneC]
    have h1 : (1 / ((σ : ℂ) - (β₁ : ℂ))).re = 1 / (σ - β₁) := by
      rw [← Complex.ofReal_sub, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    have h2 : (1 / ((σ : ℂ) - (β₂ : ℂ))).re = 1 / (σ - β₂) := by
      rw [← Complex.ofReal_sub, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [h1, h2]
  rw [hsum_S] at hlandau
  have hbound_L : (negLogDerivL χ (σ : ℂ)).re ≤
      8 * Real.log M - (3 / 2) / (σ - β) := by
    unfold negLogDerivL
    have h8 : (4 : ℝ) / (1 / 2) = 8 := by norm_num
    rw [h8] at hlandau
    have hd1 : 1 / (σ - β) ≤ 1 / (σ - β₁) :=
      one_div_le_one_div_of_le (by linarith) (by linarith [min_le_left β₁ β₂])
    have hd2 : 1 / (σ - β) ≤ 1 / (σ - β₂) :=
      one_div_le_one_div_of_le (by linarith) (by linarith [min_le_right β₁ β₂])
    have h32 : (3 / 2 : ℝ) / (σ - β) = (3 / 4) * (1 / (σ - β) + 1 / (σ - β)) := by ring
    have hcomb : (3 / 2 : ℝ) / (σ - β) ≤ (3 / 4) * (1 / (σ - β₁) + 1 / (σ - β₂)) := by linarith
    linarith
  have hbound_Z : (negLogDerivZeta (σ : ℂ)).re ≤ 1 / δ + 1 := by
    have h := negLogDerivZeta_real_le hσ1
    have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
    rwa [hσ_sub] at h
  have hpos := two_char_negLogDeriv_re_nonneg χ hσ1
  -- Bound `log M ≤ log 7200 + 2 * L`
  have hlogM : Real.log M ≤ Real.log 7200 + 2 * L := by
    have hM_eq : M = 7200 * (q : ℝ) * L := by dsimp only [M, δ]; field_simp [hL_pos.ne']; ring
    have hL_le : L ≤ 2 * (q : ℝ) :=
      (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hM_le : M ≤ 7200 * (2 * (q : ℝ)) ^ 2 := by
      rw [hM_eq]; nlinarith
    calc Real.log M ≤ Real.log (7200 * (2 * (q : ℝ)) ^ 2) := Real.log_le_log (by linarith) hM_le
      _ = Real.log 7200 + Real.log ((2 * (q : ℝ)) ^ 2) :=
          Real.log_mul (by norm_num) (by positivity)
      _ = Real.log 7200 + 2 * L := by rw [Real.log_pow]; push_cast; rfl
  have hlog7200 : Real.log 7200 < 13 := by
    have h1 := Real.log_le_log (by norm_num : (0 : ℝ) < 7200) (by norm_num : (7200 : ℝ) ≤ 2 ^ 13)
    rw [Real.log_pow] at h1
    norm_num at h1
    have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have herr : 1 + 8 * Real.log M < 1 / (4 * δ) := by
    have h150 : 150 * L = 1 / (4 * δ) := by dsimp only [δ]; field_simp [hL_pos.ne']; ring
    have hlog_nn : 0 ≤ Real.log (7200 : ℝ) := Real.log_nonneg (by norm_num)
    have hcomb : 1 + 8 * Real.log M ≤ (17 + 8 * Real.log 7200) * L := by nlinarith
    have hnum : 17 + 8 * Real.log 7200 < 150 := by linarith
    have hlt := mul_lt_mul_of_pos_right hnum hL_pos
    linarith
  have hineq : (3 / 2 : ℝ) / (σ - β) < 5 / (4 * δ) := by
    have h54 : 1 / δ + 1 / (4 * δ) = 5 / (4 * δ) := by field_simp [hδ0.ne']; ring
    linarith
  have hσβ_pos : 0 < σ - β := by
    have : β < 1 := lt_of_le_of_lt (min_le_left β₁ β₂) hβ1_lt1
    linarith
  have hmul := (div_lt_div_iff₀ hσβ_pos (by positivity : (0 : ℝ) < 4 * δ)).mp hineq
  have hβ_lt : β < 1 - δ / 5 := by dsimp only [σ] at hmul; linarith
  linarith

/-- Helper numerical closing inequality for Page's 4-character theorem:
`59 + 24 * Real.log 12000 < 500`. -/
private lemma numerical_page_closing : 59 + 24 * Real.log (12000 : ℝ) < 500 := by
  have h1 := Real.log_le_log (by norm_num : (0 : ℝ) < 12000) (by norm_num : (12000 : ℝ) ≤ 2 ^ 14)
  rw [Real.log_pow] at h1
  norm_num at h1
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  linarith

/-- **UNCONDITIONAL CONCRETE PAGE–LANDAU TWO-CHARACTER THEOREM (EXPLICIT CONSTANT `1 / 3000`,
`0` ASSUMPTIONS!)**:
for EVERY `Q ≥ 2`, ANY two distinct non-principal primitive real characters `χ₁ mod q₁`, `χ₂ mod q₂`
with `q₁ ≤ Q`, `q₂ ≤ Q`, and ANY real zeros `β₁, β₂ : ℝ` of `LFunction χ₁`, `LFunction χ₂`:
`min β₁ β₂ ≤ 1 - 1 / (3000 * Real.log (2 * Q))`. -/
theorem page_landau_two_distinct_nonprincipal_real_explicit {Q : ℝ} (hQ : 2 ≤ Q)
    {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (hq1 : (q₁ : ℝ) ≤ Q) (hq2 : (q₂ : ℝ) ≤ Q)
    (hprim1 : χ₁.IsPrimitive) (hprim2 : χ₂.IsPrimitive)
    (h1_ne : χ₁ ≠ 1) (h2_ne : χ₂ ≠ 1)
    (hreal1 : ∀ a, (χ₁ a).im = 0) (hreal2 : ∀ a, (χ₂ a).im = 0)
    (hne : PChar.of χ₁ ≠ PChar.of χ₂)
    {β₁ β₂ : ℝ}
    (hz1 : DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0)
    (hz2 : DirichletCharacter.LFunction χ₂ (β₂ : ℂ) = 0) :
    min β₁ β₂ ≤ 1 - 1 / (3000 * Real.log (2 * Q)) := by
  by_contra hgt; push Not at hgt
  have hlog4 : (1.38 : ℝ) < Real.log 4 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_gt_d9]
  set L : ℝ := Real.log (2 * Q)
  have hL : (1.38 : ℝ) < L := lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) (by linarith))
  have hL_pos : 0 < L := by linarith
  set δ : ℝ := 1 / (1000 * L)
  have hδ0 : 0 < δ := by positivity
  have hδ_le : δ ≤ 1 / 4 := by
    dsimp only [δ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hδ_small : δ < 1 / 1000 := by
    dsimp only [δ]; rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  set σ : ℝ := 1 + δ
  have hσ1 : 1 < σ := by linarith
  have hβ1_lt1 : β₁ < 1 := by
    by_contra h; push Not at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ₁ (.inl h1_ne) (by simpa using h) hz1
  have hβ2_lt1 : β₂ < 1 := by
    by_contra h; push Not at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ₂ (.inl h2_ne) (by simpa using h) hz2
  set β : ℝ := min β₁ β₂
  have hβ_gt : 1 - δ / 3 < β := by
    have hδ3 : δ / 3 = 1 / (3000 * L) := by dsimp only [δ]; field_simp [hL_pos.ne']; ring
    linarith
  have hσβ1_le : σ - β₁ ≤ 1 / 4 := by
    have : β ≤ β₁ := min_le_left β₁ β₂
    dsimp only [σ]; linarith
  have hσβ2_le : σ - β₂ ≤ 1 / 4 := by
    have : β ≤ β₂ := min_le_right β₁ β₂
    dsimp only [σ]; linarith
  have hβ1_mem : (β₁ : ℂ) ∈ Metric.closedBall (σ : ℂ) (1 / 4) := by
    rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hβ2_mem : (β₂ : ℂ) ∈ Metric.closedBall (σ : ℂ) (1 / 4) := by
    rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  -- Non-principality of `prodChar χ₁ χ₂` via `PChar`
  set ψ₁ : PChar := ⟨q₁, χ₁, hprim1⟩
  set ψ₂ : PChar := ⟨q₂, χ₂, hprim2⟩
  have hψ_ne : ψ₁ ≠ ψ₂ := by
    intro heq
    apply hne
    rw [show PChar.of χ₁ = ψ₁ from PChar.of_self ψ₁,
      show PChar.of χ₂ = ψ₂ from PChar.of_self ψ₂, heq]
  have h12_ne : prodChar χ₁ χ₂ ≠ 1 :=
    prodChar_ne_one_of_distinct_primitive_real (ψ₁ := ψ₁) (ψ₂ := ψ₂) hreal1 hψ_ne
  -- Landau bounds for `χ₁`, `χ₂`, and `prodChar χ₁ χ₂`
  obtain ⟨hM1_ge1, han1, hnz1, hbd1, hzeros1⟩ :=
    LFunction_landau_setup_real h1_ne hq1 hδ0 hδ_le
  obtain ⟨hM2_ge1, han2, hnz2, hbd2, hzeros2⟩ :=
    LFunction_landau_setup_real h2_ne hq2 hδ0 hδ_le
  have hq12 : ((q₁ * q₂ : ℕ) : ℝ) ≤ Q ^ 2 := by
    push_cast
    have hq1_nn : (0 : ℝ) ≤ (q₁ : ℝ) := Nat.cast_nonneg q₁
    have hq2_nn : (0 : ℝ) ≤ (q₂ : ℝ) := Nat.cast_nonneg q₂
    nlinarith
  obtain ⟨hM12_ge1, han12, hnz12, hbd12, hzeros12⟩ :=
    LFunction_landau_setup_real h12_ne hq12 hδ0 hδ_le
  set M₁ : ℝ := 12 * Q / δ
  set M₁₂ : ℝ := 12 * Q ^ 2 / δ
  have hlandau1 := landau_negLogDeriv_le_one_zero (r := 1 / 4) (R := 1 / 2)
    (by norm_num) (by norm_num) hM1_ge1 han1 hnz1 hbd1 hzeros1 hβ1_mem hz1
  have hlandau2 := landau_negLogDeriv_le_one_zero (r := 1 / 4) (R := 1 / 2)
    (by norm_num) (by norm_num) hM2_ge1 han2 hnz2 hbd2 hzeros2 hβ2_mem hz2
  have hlandau12 := landau_negLogDeriv_le (r := 1 / 4) (R := 1 / 2)
    (by norm_num) (by norm_num) hM12_ge1 han12 hnz12 hbd12 hzeros12
  have hre_inv1 : (1 / ((σ : ℂ) - (β₁ : ℂ))).re = 1 / (σ - β₁) := by
    rw [← Complex.ofReal_sub, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hre_inv2 : (1 / ((σ : ℂ) - (β₂ : ℂ))).re = 1 / (σ - β₂) := by
    rw [← Complex.ofReal_sub, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have herr1 : ((σ : ℂ) - (β₁ : ℂ)).re / (1 / 2 : ℝ) ^ 2 ≤ 1 := by
    simp only [Complex.sub_re, Complex.ofReal_re]; norm_num; linarith
  have herr2 : ((σ : ℂ) - (β₂ : ℂ)).re / (1 / 2 : ℝ) ^ 2 ≤ 1 := by
    simp only [Complex.sub_re, Complex.ofReal_re]; norm_num; linarith
  have h8 : (2 : ℝ) / (1 / 4) = 8 := by norm_num
  have hbound1 : (negLogDerivL χ₁ (σ : ℂ)).re ≤ 8 * Real.log M₁ + 1 - 1 / (σ - β₁) := by
    unfold negLogDerivL; rw [hre_inv1, h8] at hlandau1; linarith
  have hbound2 : (negLogDerivL χ₂ (σ : ℂ)).re ≤ 8 * Real.log M₁ + 1 - 1 / (σ - β₂) := by
    unfold negLogDerivL; rw [hre_inv2, h8] at hlandau2; linarith
  have hbound12 : (negLogDerivL (prodChar χ₁ χ₂) (σ : ℂ)).re ≤ 8 * Real.log M₁₂ := by
    unfold negLogDerivL; rwa [h8] at hlandau12
  have hboundZ : (negLogDerivZeta (σ : ℂ)).re ≤ 1 / δ + 1 := by
    have h := negLogDerivZeta_real_le hσ1
    have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
    rwa [hσ_sub] at h
  -- 4-character positivity
  have hpos := four_char_real_negLogDeriv_re_nonneg hreal1 hreal2 hσ1
  -- Bound `log M₁ ≤ log 12000 + 2 * L` and `log M₁₂ ≤ log 12000 + 3 * L`
  have hL_le_2Q : L ≤ 2 * Q := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hlogM1 : Real.log M₁ ≤ Real.log 12000 + 2 * L := by
    have hM1_eq : M₁ = 12000 * Q * L := by dsimp only [M₁, δ]; field_simp [hL_pos.ne']; ring
    have hM1_le : M₁ ≤ 12000 * (2 * Q) ^ 2 := by rw [hM1_eq]; nlinarith
    calc Real.log M₁ ≤ Real.log (12000 * (2 * Q) ^ 2) := Real.log_le_log (by linarith) hM1_le
      _ = Real.log 12000 + Real.log ((2 * Q) ^ 2) := Real.log_mul (by norm_num) (by positivity)
      _ = Real.log 12000 + 2 * L := by rw [Real.log_pow]; push_cast; rfl
  have hlogM12 : Real.log M₁₂ ≤ Real.log 12000 + 3 * L := by
    have hM12_eq : M₁₂ = 12000 * Q ^ 2 * L := by dsimp only [M₁₂, δ]; field_simp [hL_pos.ne']; ring
    have hM12_le : M₁₂ ≤ 12000 * (2 * Q) ^ 3 := by rw [hM12_eq]; nlinarith [sq_nonneg Q]
    calc Real.log M₁₂ ≤ Real.log (12000 * (2 * Q) ^ 3) := Real.log_le_log (by linarith) hM12_le
      _ = Real.log 12000 + Real.log ((2 * Q) ^ 3) := Real.log_mul (by norm_num) (by positivity)
      _ = Real.log 12000 + 3 * L := by rw [Real.log_pow]; push_cast; rfl
  -- Strict closing bound `3 + 16 log M₁ + 8 log M₁₂ < 1 / (2 * δ)`
  have herr_tot : 3 + 16 * Real.log M₁ + 8 * Real.log M₁₂ < 1 / (2 * δ) := by
    have h500 : 500 * L = 1 / (2 * δ) := by dsimp only [δ]; field_simp [hL_pos.ne']; ring
    have hlog_nn : 0 ≤ Real.log (12000 : ℝ) := Real.log_nonneg (by norm_num)
    have hcomb : 3 + 16 * Real.log M₁ + 8 * Real.log M₁₂ ≤ (59 + 24 * Real.log 12000) * L := by
      nlinarith
    have hlt := mul_lt_mul_of_pos_right numerical_page_closing hL_pos
    linarith
  have hd1 : 1 / (σ - β) ≤ 1 / (σ - β₁) :=
    one_div_le_one_div_of_le (by linarith) (by linarith [min_le_left β₁ β₂])
  have hd2 : 1 / (σ - β) ≤ 1 / (σ - β₂) :=
    one_div_le_one_div_of_le (by linarith) (by linarith [min_le_right β₁ β₂])
  have hineq : 2 / (σ - β) < 3 / (2 * δ) := by
    have h2 : 2 / (σ - β) = 1 / (σ - β) + 1 / (σ - β) := by ring
    have h32 : 1 / δ + 1 / (2 * δ) = 3 / (2 * δ) := by field_simp [hδ0.ne']; ring
    linarith
  have hσβ_pos : 0 < σ - β := by
    have : β < 1 := lt_of_le_of_lt (min_le_left β₁ β₂) hβ1_lt1
    linarith
  have hmul := (div_lt_div_iff₀ hσβ_pos (by positivity : (0 : ℝ) < 2 * δ)).mp hineq
  have hβ_lt : β < 1 - δ / 3 := by dsimp only [σ] at hmul; linarith
  linarith

/-- Helper: if `χ` is primitive and `χ = 1`, then `q = 1` and `LFunction χ = riemannZeta`, so any
real zero `β` satisfies `β < 1 - c₀ / Real.log (2 * Q)` using
`Stage5ZetaZeroFree.riemannZeta_deLaValleePoussin_zeroFree`. -/
private lemma real_zero_lt_of_primitive_eq_one {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hzf : ∀ s : ℂ, 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0)
    {Q : ℝ} (hQ : 2 ≤ Q) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (h1 : χ = 1) {β : ℝ}
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    β ≤ 1 - c₀ / Real.log (2 * Q) := by
  have hq1 : q = 1 := by
    have hc : χ.conductor = q := hprim
    rw [h1, DirichletCharacter.conductor_one] at hc
    exact hc.symm
  subst hq1
  rw [DirichletCharacter.LFunction_modOne_eq] at hzero
  have hβ_lt1 : β < 1 := by
    by_contra hge; push Not at hge
    exact riemannZeta_ne_zero_of_one_le_re (by simpa using hge) hzero
  have hne1 : (β : ℂ) ≠ 1 := fun h => hβ_lt1.ne (by simpa using congrArg Complex.re h)
  have hlt : β < 1 - c₀ / Real.log 2 := by
    by_contra hge; push Not at hge
    exact hzf (β : ℂ) (by simpa using hge) hne1 hzero
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_le : Real.log 2 ≤ Real.log (2 * Q) := Real.log_le_log (by norm_num) (by linarith)
  have hdiv : c₀ / Real.log (2 * Q) ≤ c₀ / Real.log 2 :=
    div_le_div_of_nonneg_left hc₀ hlog2 hlog_le
  linarith

/-- **UNCONDITIONAL PAGE'S UNIFORM THEOREM DIRECTLY ON MATHLIB'S `DirichletCharacter.LFunction`**
(real-threshold `Q : ℝ` form, `0` assumptions!):
`∃ c > 0`, for EVERY `Q : ℝ` with `2 ≤ Q`, EVERY two distinct real primitive characters
`χ₁ mod q₁`, `χ₂ mod q₂` (`q₁ ≤ Q`, `q₂ ≤ Q`, `PChar.of χ₁ ≠ PChar.of χ₂`), and ANY real zeros
`β₁, β₂ : ℝ` of `LFunction χ₁`, `LFunction χ₂`:
`min β₁ β₂ ≤ 1 - c / Real.log (2 * Q)`. -/
theorem page_uniform_exceptional_zero_isolation_real :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Q : ℝ), 2 ≤ Q →
        ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
          (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂),
          (q₁ : ℝ) ≤ Q → (q₂ : ℝ) ≤ Q →
          χ₁.IsPrimitive → χ₂.IsPrimitive →
          (∀ a, (χ₁ a).im = 0) → (∀ a, (χ₂ a).im = 0) →
          PChar.of χ₁ ≠ PChar.of χ₂ →
          ∀ β₁ β₂ : ℝ,
            DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
            DirichletCharacter.LFunction χ₂ (β₂ : ℂ) = 0 →
            min β₁ β₂ ≤ 1 - c / Real.log (2 * Q) := by
  obtain ⟨c₀, hc₀, hzf⟩ := riemannZeta_deLaValleePoussin_zeroFree
  set c : ℝ := min c₀ (1 / 3000)
  have hc_pos : 0 < c := by positivity
  refine ⟨c, hc_pos, fun Q hQ q₁ q₂ _ _ χ₁ χ₂ hq1 hq2 hprim1 hprim2 hreal1 hreal2 hne β₁ β₂ hz1 hz2 => ?_⟩
  have hL_pos : 0 < Real.log (2 * Q) := Real.log_pos (by linarith)
  by_cases h1 : χ₁ = 1
  · have hβ1 := real_zero_lt_of_primitive_eq_one hc₀.le hzf hQ hprim1 h1 hz1
    have hdiv : c / Real.log (2 * Q) ≤ c₀ / Real.log (2 * Q) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hL_pos.le
    exact (min_le_left β₁ β₂).trans (by linarith)
  · by_cases h2 : χ₂ = 1
    · have hβ2 := real_zero_lt_of_primitive_eq_one hc₀.le hzf hQ hprim2 h2 hz2
      have hdiv : c / Real.log (2 * Q) ≤ c₀ / Real.log (2 * Q) :=
        div_le_div_of_nonneg_right (min_le_left _ _) hL_pos.le
      exact (min_le_right β₁ β₂).trans (by linarith)
    · have hpage := page_landau_two_distinct_nonprincipal_real_explicit hQ hq1 hq2 hprim1 hprim2
        h1 h2 hreal1 hreal2 hne hz1 hz2
      have hdiv : c / Real.log (2 * Q) ≤ 1 / (3000 * Real.log (2 * Q)) := by
        have h1' : (1 / 3000 : ℝ) / Real.log (2 * Q) = 1 / (3000 * Real.log (2 * Q)) := by ring
        rw [← h1']
        exact div_le_div_of_nonneg_right (min_le_right _ _) hL_pos.le
      linarith

/-- **UNCONDITIONAL PAGE'S UNIFORM THEOREM DIRECTLY ON MATHLIB'S `DirichletCharacter.LFunction`**
(`Q : ℕ` form, `0` assumptions!):
`∃ c > 0, ∀ Q ≥ 2, ∀ q₁ q₂ [NeZero q₁] [NeZero q₂] (χ₁ : DirichletCharacter ℂ q₁)
  (χ₂ : DirichletCharacter ℂ q₂), q₁ ≤ Q → q₂ ≤ Q → χ₁.IsPrimitive → χ₂.IsPrimitive →
  (∀ a, (χ₁ a).im = 0) → (∀ a, (χ₂ a).im = 0) → PChar.of χ₁ ≠ PChar.of χ₂ →
  ∀ β₁ β₂ : ℝ, LFunction χ₁ β₁ = 0 → LFunction χ₂ β₂ = 0 →
  min β₁ β₂ ≤ 1 - c / Real.log (2 * Q)`. -/
theorem page_uniform_exceptional_zero_isolation :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Q : ℕ), 2 ≤ Q →
        ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
          (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂),
          q₁ ≤ Q → q₂ ≤ Q →
          χ₁.IsPrimitive → χ₂.IsPrimitive →
          (∀ a, (χ₁ a).im = 0) → (∀ a, (χ₂ a).im = 0) →
          PChar.of χ₁ ≠ PChar.of χ₂ →
          ∀ β₁ β₂ : ℝ,
            DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
            DirichletCharacter.LFunction χ₂ (β₂ : ℂ) = 0 →
            min β₁ β₂ ≤ 1 - c / Real.log (2 * (Q : ℝ)) := by
  obtain ⟨c, hc, hpage⟩ := page_uniform_exceptional_zero_isolation_real
  exact ⟨c, hc, fun Q hQ q₁ q₂ _ _ χ₁ χ₂ hq1 hq2 =>
    hpage (Q : ℝ) (by exact_mod_cast hQ) q₁ q₂ χ₁ χ₂ (by exact_mod_cast hq1) (by exact_mod_cast hq2)⟩

/-- **PAGE'S FULL AT-MOST-ONE SIEGEL-ZERO UNIQUENESS THEOREM (ALL PRIMITIVE CHARACTERS, REAL OR
COMPLEX, `0` ASSUMPTIONS!)**:
`∃ c > 0`, for EVERY `Q ≥ 2`, among ALL primitive Dirichlet characters `ψ : PChar` of conductor
`ψ.N ≤ Q` (both real AND complex!) and ALL real `β : ℝ`:
1. Any `(ψ, β)` with `LFunction ψ.χ β = 0` and `1 - c / Real.log (2 * Q) < β` must be a
   non-principal real character (`ψ.IsReal ∧ ψ.χ ≠ 1`), and
2. There is AT MOST ONE such pair `(ψ, β)` (i.e., if `(ψ₁, β₁)` and `(ψ₂, β₂)` both satisfy this,
   then `ψ₁ = ψ₂ ∧ β₁ = β₂`). -/
theorem page_at_most_one_siegel_zero_unconditional :
    ∃ c : ℝ, 0 < c ∧
      (∀ (Q : ℕ), 2 ≤ Q →
        ∀ (ψ : PChar) (β : ℝ), ψ.N ≤ Q →
          DirichletCharacter.LFunction ψ.χ (β : ℂ) = 0 →
          1 - c / Real.log (2 * (Q : ℝ)) < β →
          ψ.IsReal ∧ ψ.χ ≠ 1) ∧
      (∀ (Q : ℕ), 2 ≤ Q →
        ∀ (ψ₁ ψ₂ : PChar) (β₁ β₂ : ℝ), ψ₁.N ≤ Q → ψ₂.N ≤ Q →
          DirichletCharacter.LFunction ψ₁.χ (β₁ : ℂ) = 0 →
          DirichletCharacter.LFunction ψ₂.χ (β₂ : ℂ) = 0 →
          1 - c / Real.log (2 * (Q : ℝ)) < β₁ →
          1 - c / Real.log (2 * (Q : ℝ)) < β₂ →
          ψ₁ = ψ₂ ∧ β₁ = β₂) := by
  obtain ⟨c₀, hc₀, hzf⟩ := riemannZeta_deLaValleePoussin_zeroFree
  set c : ℝ := min c₀ (1 / 14000)
  have hc_pos : 0 < c := by positivity
  have hreal_and_ne :
      ∀ (Q : ℕ), 2 ≤ Q →
        ∀ (ψ : PChar) (β : ℝ), ψ.N ≤ Q →
          DirichletCharacter.LFunction ψ.χ (β : ℂ) = 0 →
          1 - c / Real.log (2 * (Q : ℝ)) < β →
          ψ.IsReal ∧ ψ.χ ≠ 1 := by
    intro Q hQ ψ β hN hzero hβ
    have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    have hL_pos : 0 < Real.log (2 * (Q : ℝ)) := Real.log_pos (by linarith)
    have hsq : ψ.χ ^ 2 = 1 := by
      by_contra hχ2
      have hq_pos : (0 : ℝ) < (ψ.N : ℝ) := Nat.cast_pos.mpr (NeZero.pos ψ.N)
      have hlog_le : Real.log ((ψ.N : ℝ) * (|(β : ℂ).im| + 2)) ≤ Real.log (2 * (Q : ℝ)) := by
        simp only [Complex.ofReal_im, abs_zero, zero_add]
        exact Real.log_le_log (by positivity) (by nlinarith [show (ψ.N : ℝ) ≤ (Q : ℝ) by exact_mod_cast hN])
      have hq2 : 2 ≤ ψ.N :=
        two_le_of_dirichletChar_ne_one (χ := ψ.χ) (fun h1 => hχ2 (by rw [h1]; exact one_pow 2))
      have hlog_pos : 0 < Real.log ((ψ.N : ℝ) * (|(β : ℂ).im| + 2)) := by
        simp only [Complex.ofReal_im, abs_zero, zero_add]
        exact Real.log_pos (by exact_mod_cast (by omega : 1 < ψ.N * 2))
      have hdiv : 1 / (14000 * Real.log (2 * (Q : ℝ))) ≤
          1 / (14000 * Real.log ((ψ.N : ℝ) * (|(β : ℂ).im| + 2))) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have hc_le : c / Real.log (2 * (Q : ℝ)) ≤ 1 / (14000 * Real.log (2 * (Q : ℝ))) := by
        have h1 : (1 / 14000 : ℝ) / Real.log (2 * (Q : ℝ)) = 1 / (14000 * Real.log (2 * (Q : ℝ))) := by ring
        rw [← h1]
        exact div_le_div_of_nonneg_right (min_le_right _ _) hL_pos.le
      exact LFunction_complex_char_deLaValleePoussin_zeroFree ψ.χ hχ2
        (by simp only [Complex.ofReal_re]; linarith) hzero
    have hreal : ψ.IsReal := isRealChar_of_sq_eq_one hsq
    have hne1 : ψ.χ ≠ 1 := by
      intro h1
      have hle := real_zero_lt_of_primitive_eq_one hc₀.le hzf hQR ψ.prim h1 hzero
      have hc_le : c / Real.log (2 * (Q : ℝ)) ≤ c₀ / Real.log (2 * (Q : ℝ)) :=
        div_le_div_of_nonneg_right (min_le_left _ _) hL_pos.le
      linarith
    exact ⟨hreal, hne1⟩
  refine ⟨c, hc_pos, hreal_and_ne, ?_⟩
  intro Q hQ ψ₁ ψ₂ β₁ β₂ hN1 hN2 hz1 hz2 hβ1 hβ2
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hL_pos : 0 < Real.log (2 * (Q : ℝ)) := Real.log_pos (by linarith)
  obtain ⟨hreal1, hne1⟩ := hreal_and_ne Q hQ ψ₁ β₁ hN1 hz1 hβ1
  obtain ⟨hreal2, hne2⟩ := hreal_and_ne Q hQ ψ₂ β₂ hN2 hz2 hβ2
  have hψ_eq : ψ₁ = ψ₂ := by
    by_contra hne
    have hof_ne : PChar.of ψ₁.χ ≠ PChar.of ψ₂.χ := by
      rwa [PChar.of_self ψ₁, PChar.of_self ψ₂]
    have hpage := page_landau_two_distinct_nonprincipal_real_explicit hQR
      (by exact_mod_cast hN1) (by exact_mod_cast hN2) ψ₁.prim ψ₂.prim hne1 hne2 hreal1 hreal2
      hof_ne hz1 hz2
    have hc_le : c / Real.log (2 * (Q : ℝ)) ≤ 1 / (3000 * Real.log (2 * (Q : ℝ))) := by
      have h1 : c ≤ 1 / 3000 := (min_le_right _ _).trans (by norm_num)
      have h2 : (1 / 3000 : ℝ) / Real.log (2 * (Q : ℝ)) = 1 / (3000 * Real.log (2 * (Q : ℝ))) := by ring
      rw [← h2]
      exact div_le_div_of_nonneg_right h1 hL_pos.le
    have hmin_gt : 1 - c / Real.log (2 * (Q : ℝ)) < min β₁ β₂ := lt_min hβ1 hβ2
    linarith
  refine ⟨hψ_eq, ?_⟩
  subst hψ_eq
  by_contra hβ_ne
  have hsingle := LFunction_real_char_at_most_one_real_zero_unconditional hne1 hβ_ne hz1 hz2
  have hq2 : 2 ≤ ψ₁.N := two_le_of_dirichletChar_ne_one hne1
  have hlog1_pos : 0 < Real.log (2 * (ψ₁.N : ℝ)) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * ψ₁.N))
  have hlog_le : Real.log (2 * (ψ₁.N : ℝ)) ≤ Real.log (2 * (Q : ℝ)) :=
    Real.log_le_log (by positivity) (by nlinarith [show (ψ₁.N : ℝ) ≤ (Q : ℝ) by exact_mod_cast hN1])
  have hdiv : 1 / (3000 * Real.log (2 * (Q : ℝ))) ≤ 1 / (3000 * Real.log (2 * (ψ₁.N : ℝ))) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hc_le : c / Real.log (2 * (Q : ℝ)) ≤ 1 / (3000 * Real.log (2 * (Q : ℝ))) := by
    have h1 : c ≤ 1 / 3000 := (min_le_right _ _).trans (by norm_num)
    have h2 : (1 / 3000 : ℝ) / Real.log (2 * (Q : ℝ)) = 1 / (3000 * Real.log (2 * (Q : ℝ))) := by ring
    rw [← h2]
    exact div_le_div_of_nonneg_right h1 hL_pos.le
  have hmin_gt : 1 - c / Real.log (2 * (Q : ℝ)) < min β₁ β₂ := lt_min hβ1 hβ2
  linarith

/-- **Master Unconditional Stage 7 Theorem (Effective Dirichlet Lower Bounds, Real-Zero Exclusion &
Page's Uniform Theorem on Mathlib's `DirichletCharacter.LFunction`, `0` Assumptions!)**. -/
theorem stage7_siegelWalfisz_unconditional :
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ.Odd → (∀ a : ZMod q, (χ a).im = 0) →
      Real.pi / ((q : ℝ) * Real.sqrt (q : ℝ)) ≤ (DirichletCharacter.LFunction χ 1).re) ∧
    (∀ (q : ℕ) [NeZero q], Odd q → 5 ≤ q →
      ∀ (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ.Odd → (∀ a : ZMod q, (χ a).im = 0) →
        Real.pi / Real.sqrt (q : ℝ) ≤ (DirichletCharacter.LFunction χ 1).re) ∧
    (∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → (∀ a, (χ a).im = 0) → χ.Odd →
        ∀ β : ℝ,
          1 - c / ((q : ℝ) * Real.sqrt (q : ℝ) * (Real.log (2 * (q : ℝ))) ^ 2) ≤ β →
          DirichletCharacter.LFunction χ (β : ℂ) ≠ 0) ∧
    (∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], Odd q →
        ∀ (χ : DirichletCharacter ℂ q),
          χ.IsPrimitive → (∀ a, (χ a).im = 0) → χ.Odd →
          ∀ β : ℝ,
            1 - c / (Real.sqrt (q : ℝ) * (Real.log (2 * (q : ℝ))) ^ 2) ≤ β →
            DirichletCharacter.LFunction χ (β : ℂ) ≠ 0) ∧
    (∃ c : ℝ, 0 < c ∧
      ∀ (Q : ℕ), 2 ≤ Q →
        ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
          (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂),
          q₁ ≤ Q → q₂ ≤ Q →
          χ₁.IsPrimitive → χ₂.IsPrimitive →
          (∀ a, (χ₁ a).im = 0) → (∀ a, (χ₂ a).im = 0) →
          PChar.of χ₁ ≠ PChar.of χ₂ →
          ∀ β₁ β₂ : ℝ,
            DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
            DirichletCharacter.LFunction χ₂ (β₂ : ℂ) = 0 →
            min β₁ β₂ ≤ 1 - c / Real.log (2 * (Q : ℝ))) :=
  ⟨fun _ _ _ hprim hodd hreal => LFunction_one_ge_pi_div_q_sqrt_q hprim hodd hreal,
   fun _ _ hodd_q hq5 _ hprim hodd hreal => LFunction_one_ge_pi_div_sqrt_q hodd_q hq5 hprim hodd hreal,
   LFunction_odd_real_primitive_zeroFree_real,
   LFunction_odd_real_primitive_odd_cond_zeroFree_real,
   page_uniform_exceptional_zero_isolation⟩

end RHDirect.Stage7SiegelWalfisz
