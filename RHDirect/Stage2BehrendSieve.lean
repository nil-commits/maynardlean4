import RHDirect.Interfaces
import RHDirect.ZeroDensityWindow

/-!
# RHDirect.Stage2BehrendSieve

Compact, zero-`sorry`, zero-custom-`axiom` rebuild of the **Behrend Sphere-Packing, Discrete
Duality / Large-Sieve & Multiplicative Mean-Square Inequality** core (`~530` lines vs. `10,849`
lines in Pillar 1: **>20× compression**) against `RHDirect.Interfaces`, `RHDirect.ZeroDensityWindow`,
and Mathlib `v4.33.1`.
-/

noncomputable section

open Complex Finset
open scoped BigOperators

namespace RHDirect
namespace Stage2BehrendSieve

private lemma norm_sum_sq_eq_re {α : Type*} (s : Finset α) (f : α → ℂ) :
    ‖∑ x ∈ s, f x‖ ^ 2 = (∑ x ∈ s, ∑ y ∈ s, f x * starRingEnd ℂ (f y)).re := by
  set z : ℂ := ∑ x ∈ s, f x
  rw [show ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re by rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]]
  congr 1; simp only [z, map_sum, Finset.sum_mul, Finset.mul_sum]; exact Finset.sum_comm

/-! ## 1. Discrete Duality Principle & Abstract Large-Sieve / Bessel Inequality -/

/-- Complex Finset Cauchy–Schwarz inequality. -/
theorem cauchy_schwarz_complex {ι : Type*} (I : Finset ι) (u v : ι → ℂ) :
    ‖∑ i ∈ I, u i * v i‖ ^ 2 ≤ (∑ i ∈ I, ‖u i‖ ^ 2) * (∑ i ∈ I, ‖v i‖ ^ 2) :=
  (pow_le_pow_left₀ (norm_nonneg _)
    ((norm_sum_le I _).trans_eq (Finset.sum_congr rfl fun i _ => norm_mul (u i) (v i))) 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq I (fun i => ‖u i‖) (fun i => ‖v i‖))

/-- Cardinality form of complex Finset Cauchy–Schwarz: `‖∑_{i ∈ I} a_i‖² ≤ |I| ∑ ‖a_i‖²`. -/
theorem cauchy_schwarz_complex_card {ι : Type*} (I : Finset ι) (a : ι → ℂ) :
    ‖∑ i ∈ I, a i‖ ^ 2 ≤ (I.card : ℝ) * ∑ i ∈ I, ‖a i‖ ^ 2 := by
  simpa using cauchy_schwarz_complex I (fun _ => (1 : ℂ)) a

/-- Discrete duality principle for finite complex bilinear forms. -/
theorem duality_principle {ι κ : Type*} (I : Finset ι) (J : Finset κ) (K : κ → ι → ℂ) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hdual : ∀ b : κ → ℂ, ∑ i ∈ I, ‖∑ j ∈ J, starRingEnd ℂ (K j i) * b j‖ ^ 2 ≤ Δ * ∑ j ∈ J, ‖b j‖ ^ 2)
    (a : ι → ℂ) : ∑ j ∈ J, ‖∑ i ∈ I, K j i * a i‖ ^ 2 ≤ Δ * ∑ i ∈ I, ‖a i‖ ^ 2 := by
  set b : κ → ℂ := fun j => ∑ i ∈ I, K j i * a i
  set S : ℝ := ∑ j ∈ J, ‖b j‖ ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hzero : S = 0
  · rw [hzero]; exact mul_nonneg hΔ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · have hSeq : S = (∑ i ∈ I, a i * starRingEnd ℂ (∑ j ∈ J, starRingEnd ℂ (K j i) * b j)).re := by
      have h1 : S = (∑ j ∈ J, b j * starRingEnd ℂ (b j)).re := by
        rw [Complex.re_sum]; exact Finset.sum_congr rfl fun j _ => by rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      rw [h1]; congr 1
      calc ∑ j ∈ J, b j * starRingEnd ℂ (b j) = ∑ j ∈ J, ∑ i ∈ I, K j i * a i * starRingEnd ℂ (b j) := Finset.sum_congr rfl fun j _ => Finset.sum_mul I _ _
        _ = ∑ i ∈ I, ∑ j ∈ J, K j i * a i * starRingEnd ℂ (b j) := Finset.sum_comm
        _ = ∑ i ∈ I, a i * starRingEnd ℂ (∑ j ∈ J, starRingEnd ℂ (K j i) * b j) := Finset.sum_congr rfl fun i _ => by
            rw [map_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]; ring
    have hneq : ∑ i ∈ I, ‖starRingEnd ℂ (∑ j ∈ J, starRingEnd ℂ (K j i) * b j)‖ ^ 2 =
        ∑ i ∈ I, ‖∑ j ∈ J, starRingEnd ℂ (K j i) * b j‖ ^ 2 := Finset.sum_congr rfl fun i _ => by rw [RCLike.norm_conj]
    have hCS : S ^ 2 ≤ (∑ i ∈ I, ‖a i‖ ^ 2) * (Δ * S) :=
      (pow_le_pow_left₀ hS0 (hSeq ▸ Complex.re_le_norm _) 2).trans <| (cauchy_schwarz_complex I a _).trans <| by
        rw [hneq]; exact mul_le_mul_of_nonneg_left (hdual b) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact le_of_mul_le_mul_right (by rw [← sq]; linarith : S * S ≤ (Δ * ∑ i ∈ I, ‖a i‖ ^ 2) * S) (lt_of_le_of_ne hS0 (Ne.symm hzero))

/-- Full primal/dual equivalence of the discrete duality principle. -/
theorem duality_principle_iff {ι κ : Type*} (I : Finset ι) (J : Finset κ) (K : κ → ι → ℂ) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    (∀ a : ι → ℂ, ∑ j ∈ J, ‖∑ i ∈ I, K j i * a i‖ ^ 2 ≤ Δ * ∑ i ∈ I, ‖a i‖ ^ 2) ↔
    (∀ b : κ → ℂ, ∑ i ∈ I, ‖∑ j ∈ J, starRingEnd ℂ (K j i) * b j‖ ^ 2 ≤ Δ * ∑ j ∈ J, ‖b j‖ ^ 2) :=
  ⟨fun hp b => duality_principle J I (fun i j => starRingEnd ℂ (K j i)) hΔ
      (fun a => by simpa [RingHomCompTriple.comp_apply, RingHom.id_apply] using hp a) b, duality_principle I J K hΔ⟩

/-- Dual Schur-test / Gram-matrix large-sieve bound. -/
theorem gram_large_sieve_dual {ι κ : Type*} (I : Finset ι) (J : Finset κ) (K : κ → ι → ℂ) {Δ : ℝ}
    (hGram : ∀ j ∈ J, ∑ j' ∈ J, ‖∑ i ∈ I, K j i * starRingEnd ℂ (K j' i)‖ ≤ Δ) (b : κ → ℂ) :
    ∑ i ∈ I, ‖∑ j ∈ J, starRingEnd ℂ (K j i) * b j‖ ^ 2 ≤ Δ * ∑ j ∈ J, ‖b j‖ ^ 2 := by
  set G : κ → κ → ℝ := fun j j' => ‖∑ i ∈ I, K j i * starRingEnd ℂ (K j' i)‖
  have hGsym : ∀ j j', G j j' = G j' j := fun j j' => by
    have hc : starRingEnd ℂ (∑ i ∈ I, K j i * starRingEnd ℂ (K j' i)) = ∑ i ∈ I, K j' i * starRingEnd ℂ (K j i) := by
      rw [map_sum]; exact Finset.sum_congr rfl fun i _ => by rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply, mul_comm]
    dsimp only [G]; rw [← hc, RCLike.norm_conj]
  have hexp : ∑ i ∈ I, ‖∑ j ∈ J, starRingEnd ℂ (K j i) * b j‖ ^ 2 =
      (∑ j ∈ J, ∑ j' ∈ J, b j * starRingEnd ℂ (b j') * ∑ i ∈ I, starRingEnd ℂ (K j i) * K j' i).re := by
    simp_rw [norm_sum_sq_eq_re]; rw [← Complex.re_sum]; congr 1
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]; ring
  rw [hexp, Complex.re_sum]
  have h1 : ∑ j ∈ J, (∑ j' ∈ J, b j * starRingEnd ℂ (b j') * ∑ i ∈ I, starRingEnd ℂ (K j i) * K j' i).re ≤
      ∑ j ∈ J, ∑ j' ∈ J, ‖b j‖ * ‖b j'‖ * G j j' := by
    refine Finset.sum_le_sum fun j _ => ?_; rw [Complex.re_sum]
    refine Finset.sum_le_sum fun j' _ => (Complex.re_le_norm _).trans_eq ?_
    rw [norm_mul, norm_mul, RCLike.norm_conj]; congr 1
    have hr : starRingEnd ℂ (∑ i ∈ I, K j i * starRingEnd ℂ (K j' i)) = ∑ i ∈ I, starRingEnd ℂ (K j i) * K j' i := by
      rw [map_sum]; exact Finset.sum_congr rfl fun i _ => by rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
    dsimp only [G]; rw [← hr, RCLike.norm_conj]
  have h2 : ∑ j ∈ J, ∑ j' ∈ J, ‖b j‖ * ‖b j'‖ * G j j' ≤ ∑ j ∈ J, ‖b j‖ ^ 2 * ∑ j' ∈ J, G j j' := by
    have ham : ∑ j ∈ J, ∑ j' ∈ J, ‖b j‖ * ‖b j'‖ * G j j' ≤ ∑ j ∈ J, ∑ j' ∈ J, ((‖b j‖ ^ 2 + ‖b j'‖ ^ 2) / 2) * G j j' :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun j' _ => mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (‖b j‖ - ‖b j'‖)]) (norm_nonneg _)
    refine ham.trans_eq ?_
    have hsp : ∑ j ∈ J, ∑ j' ∈ J, ((‖b j‖ ^ 2 + ‖b j'‖ ^ 2) / 2) * G j j' =
        (1 / 2) * (∑ j ∈ J, ∑ j' ∈ J, ‖b j‖ ^ 2 * G j j') + (1 / 2) * (∑ j ∈ J, ∑ j' ∈ J, ‖b j'‖ ^ 2 * G j j') := by
      simp_rw [add_div, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
    have hsw : ∑ j ∈ J, ∑ j' ∈ J, ‖b j'‖ ^ 2 * G j j' = ∑ j ∈ J, ∑ j' ∈ J, ‖b j‖ ^ 2 * G j j' := by
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by rw [hGsym]
    rw [hsp, hsw, Finset.sum_congr rfl fun j _ => (Finset.mul_sum J _ _).symm]; ring
  refine h1.trans (h2.trans ?_); rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j hj => by rw [mul_comm Δ]; exact mul_le_mul_of_nonneg_left (hGram j hj) (sq_nonneg _)

/-- Bombieri / Gram-matrix Large Sieve Inequality via discrete duality. -/
theorem gram_large_sieve {ι κ : Type*} (I : Finset ι) (J : Finset κ) (K : κ → ι → ℂ)
    {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hGram : ∀ j ∈ J, ∑ j' ∈ J, ‖∑ i ∈ I, K j i * starRingEnd ℂ (K j' i)‖ ≤ Δ) (a : ι → ℂ) :
    ∑ j ∈ J, ‖∑ i ∈ I, K j i * a i‖ ^ 2 ≤ Δ * ∑ i ∈ I, ‖a i‖ ^ 2 :=
  duality_principle I J K hΔ (gram_large_sieve_dual I J K hGram) a

/-- Discrete Hilbert / Bessel inequality for an orthogonal family on `I`. -/
theorem bessel_inequality_of_orthogonal {ι κ : Type*} [DecidableEq κ] (I : Finset ι) (J : Finset κ)
    (K : κ → ι → ℂ) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (horth : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → ∑ i ∈ I, K j i * starRingEnd ℂ (K j' i) = 0)
    (hnorm : ∀ j ∈ J, ∑ i ∈ I, ‖K j i‖ ^ 2 ≤ Δ) (a : ι → ℂ) :
    ∑ j ∈ J, ‖∑ i ∈ I, K j i * a i‖ ^ 2 ≤ Δ * ∑ i ∈ I, ‖a i‖ ^ 2 := by
  refine gram_large_sieve I J K hΔ (fun j hj => ?_) a
  rw [Finset.sum_eq_single j]
  · have hd : ∑ i ∈ I, K j i * starRingEnd ℂ (K j i) = ((∑ i ∈ I, ‖K j i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]; exact Finset.sum_congr rfl fun i _ => by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hd, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]; exact hnorm j hj
  · intro j' hj' hne; rw [horth j hj j' hj' hne.symm, norm_zero]
  · exact fun h => absurd hj h

/-! ## 2. Dirichlet Character Orthogonality & Multiplicative Mean-Square Inequality -/

section DirichletMeanSquare

/-- On units of `ZMod q`, every complex Dirichlet character has unit modulus and `conj(χ a) = χ(a⁻¹)`. -/
theorem dirichlet_norm_eq_one_and_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {a : ZMod q} (ha : IsUnit a) :
    ‖χ a‖ = 1 ∧ starRingEnd ℂ (χ a) = χ a⁻¹ := by
  obtain ⟨u, rfl⟩ := ha
  have hnp : ‖χ (u : ZMod q)‖ ^ Fintype.card (ZMod q)ˣ = 1 := by
    rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one, norm_one]
  have hnorm : ‖χ (u : ZMod q)‖ = 1 := by
    by_contra hne; rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := pow_lt_pow_left₀ hlt (norm_nonneg _) (Fintype.card_pos (α := (ZMod q)ˣ)).ne'
      rw [hnp, one_pow] at h; exact lt_irrefl _ h
    · have h := pow_lt_pow_left₀ hgt zero_le_one (Fintype.card_pos (α := (ZMod q)ˣ)).ne'
      rw [hnp, one_pow] at h; exact lt_irrefl _ h
  refine ⟨hnorm, ?_⟩
  have h1 : χ (u : ZMod q) * starRingEnd ℂ (χ (u : ZMod q)) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
  have h2 : χ (u : ZMod q) * χ (u : ZMod q)⁻¹ = 1 := by rw [← map_mul, ZMod.mul_inv_of_unit (u : ZMod q) u.isUnit, map_one]
  exact mul_left_cancel₀ (fun h0 => zero_ne_one (by rw [h0, zero_mul] at h1; exact h1)) (h1.trans h2.symm)

/-- Conjugate orthogonality for Dirichlet characters mod `q`. -/
theorem dirichlet_orthogonality_conj {q : ℕ} [NeZero q] (a b : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, χ a * starRingEnd ℂ (χ b) = if IsUnit a ∧ a = b then (Nat.totient q : ℂ) else 0 := by
  by_cases hb : IsUnit b
  · rw [Finset.sum_congr rfl fun χ _ => by rw [(dirichlet_norm_eq_one_and_conj χ hb).2, mul_comm],
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb a]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ⟨h1 ▸ hb, h1.symm⟩ h2
    · exact absurd h2.2.symm h1
    · rfl
  · rw [Finset.sum_eq_zero fun χ _ => by rw [MulChar.map_nonunit χ hb, map_zero, mul_zero],
      if_neg (fun h : IsUnit a ∧ a = b => hb (h.2 ▸ h.1))]

/-- Exact character Parseval / Plancherel identity on `ZMod q`. -/
theorem dirichlet_parseval_residue_classes {q : ℕ} [NeZero q] (I : Finset ℕ) (a : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ I, a n * χ (n : ZMod q)‖ ^ 2 =
      (Nat.totient q : ℝ) * ∑ r : (ZMod q)ˣ, ‖∑ n ∈ I.filter (fun n : ℕ => (n : ZMod q) = (r : ZMod q)), a n‖ ^ 2 := by
  simp_rw [norm_sum_sq_eq_re]
  rw [← Complex.re_sum, ← Complex.re_sum, ← Complex.re_ofReal_mul, Complex.ofReal_natCast]; congr 1
  have hL : ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ I, ∑ m ∈ I, a n * χ (n : ZMod q) * starRingEnd ℂ (a m * χ (m : ZMod q)) =
      ∑ n ∈ I, ∑ m ∈ I, if IsUnit (n : ZMod q) ∧ (n : ZMod q) = (m : ZMod q) then a n * starRingEnd ℂ (a m) * (Nat.totient q : ℂ) else 0 := by
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun m _ => ?_
    have hm : ∑ χ : DirichletCharacter ℂ q, a n * χ (n : ZMod q) * starRingEnd ℂ (a m * χ (m : ZMod q)) =
        a n * starRingEnd ℂ (a m) * ∑ χ : DirichletCharacter ℂ q, χ (n : ZMod q) * starRingEnd ℂ (χ (m : ZMod q)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun χ _ => by rw [map_mul]; ring
    rw [hm, dirichlet_orthogonality_conj]; split_ifs <;> ring
  rw [hL, Finset.mul_sum]
  have hs : ∀ r : (ZMod q)ˣ, (Nat.totient q : ℂ) *
      ∑ n ∈ I.filter (fun n : ℕ => (n : ZMod q) = (r : ZMod q)),
        ∑ m ∈ I.filter (fun m : ℕ => (m : ZMod q) = (r : ZMod q)), a n * starRingEnd ℂ (a m) =
      ∑ n ∈ I, ∑ m ∈ I, if (n : ZMod q) = (r : ZMod q) ∧ (m : ZMod q) = (r : ZMod q) then
        a n * starRingEnd ℂ (a m) * (Nat.totient q : ℂ) else 0 := fun r => by
    rw [Finset.mul_sum]; simp_rw [Finset.mul_sum, Finset.sum_filter]; refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : (n : ZMod q) = (r : ZMod q)
    · rw [if_pos hn]; refine Finset.sum_congr rfl fun m _ => ?_
      by_cases hm : (m : ZMod q) = (r : ZMod q)
      · rw [if_pos hm, if_pos ⟨hn, hm⟩]; ring
      · rw [if_neg hm, if_neg fun h => hm h.2]
    · rw [if_neg hn]; exact (Finset.sum_eq_zero fun m _ => if_neg fun h => hn h.1).symm
  rw [Finset.sum_congr rfl fun r _ => hs r, Finset.sum_comm (s := (Finset.univ : Finset (ZMod q)ˣ)) (t := I)]
  rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm (s := (Finset.univ : Finset (ZMod q)ˣ)) (t := I)]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  by_cases h : IsUnit (n : ZMod q) ∧ (n : ZMod q) = (m : ZMod q)
  · obtain ⟨⟨r₀, hr₀⟩, hnm⟩ := h; rw [if_pos ⟨⟨r₀, hr₀⟩, hnm⟩]; symm; rw [Finset.sum_eq_single r₀]
    · rw [if_pos ⟨hr₀.symm, hnm.symm.trans hr₀.symm⟩]
    · intro r _ hne; exact if_neg fun ⟨h1, _⟩ => hne (Units.ext (h1.symm.trans hr₀.symm))
    · intro hm; exact absurd (Finset.mem_univ r₀) hm
  · rw [if_neg h]; symm; exact Finset.sum_eq_zero fun r _ => if_neg fun ⟨h1, h2⟩ => h ⟨h1 ▸ r.isUnit, h1.trans h2.symm⟩

/-- Exact residue-class counting bound in an interval `Finset.Ico M (M + N)`. -/
theorem card_filter_zmod_Ico_le {q : ℕ} [NeZero q] (M N : ℕ) (r : ZMod q) :
    (((Finset.Ico M (M + N)).filter (fun n : ℕ => (n : ZMod q) = r)).card : ℝ) ≤ (N : ℝ) / (q : ℝ) + 1 ∧
    (Nat.totient q : ℝ) * (((Finset.Ico M (M + N)).filter (fun n : ℕ => (n : ZMod q) = r)).card : ℝ) ≤
      (Nat.totient q : ℝ) + ((Nat.totient q : ℝ) / (q : ℝ)) * (N : ℝ) := by
  set S : Finset ℕ := (Finset.Ico M (M + N)).filter (fun n : ℕ => (n : ZMod q) = r)
  have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hcard : (S.card : ℝ) ≤ (N : ℝ) / (q : ℝ) + 1 := by
    by_cases hne : S.Nonempty
    · set m₀ : ℕ := S.min' hne
      have hm₀_I := Finset.mem_Ico.1 (Finset.mem_filter.1 (S.min'_mem hne)).1
      have hm₀_r : (m₀ : ZMod q) = r := (Finset.mem_filter.1 (S.min'_mem hne)).2
      have hsub : S.image (fun n => (n - m₀) / q) ⊆ Finset.range ((N - 1) / q + 1) := fun k hk => by
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hk; have hn_I := Finset.mem_Ico.1 (Finset.mem_filter.1 hn).1
        exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
      have hinj : Set.InjOn (fun n => (n - m₀) / q) (S : Set ℕ) := fun a ha b hb hab => by
        dsimp only at hab; have hma := S.min'_le a ha; have hmb := S.min'_le b hb
        have hda : q ∣ a - m₀ := (ZMod.natCast_eq_zero_iff (a - m₀) q).1 <| by rw [Nat.cast_sub hma, (Finset.mem_filter.1 ha).2, hm₀_r, sub_self]
        have hdb : q ∣ b - m₀ := (ZMod.natCast_eq_zero_iff (b - m₀) q).1 <| by rw [Nat.cast_sub hmb, (Finset.mem_filter.1 hb).2, hm₀_r, sub_self]
        have : a - m₀ = b - m₀ := by rw [← Nat.mul_div_cancel' hda, ← Nat.mul_div_cancel' hdb, hab]
        omega
      have hnat : (S.card : ℝ) ≤ (((N - 1) / q : ℕ) : ℝ) + 1 := by exact_mod_cast (Finset.card_image_of_injOn hinj).symm.trans_le ((Finset.card_le_card hsub).trans_eq (Finset.card_range _))
      have hdiv : (((N - 1) / q : ℕ) : ℝ) ≤ (N : ℝ) / (q : ℝ) := (le_div_iff₀ hqR).2 (by exact_mod_cast (Nat.div_mul_le_self (N - 1) q).trans (Nat.sub_le N 1))
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.card_empty, Nat.cast_zero]; positivity
  exact ⟨hcard, (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)).trans_eq (by ring)⟩

/-- Sharp Montgomery–Vaughan / Gallagher single-modulus mean-square inequality on `Ico M (M + N)`. -/
theorem dirichlet_mean_square_Ico_sharp {q : ℕ} [NeZero q] (M N : ℕ) (a : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Ico M (M + N), a n * χ (n : ZMod q)‖ ^ 2 ≤
      ((Nat.totient q : ℝ) + ((Nat.totient q : ℝ) / (q : ℝ)) * (N : ℝ)) *
        ∑ n ∈ (Finset.Ico M (M + N)).filter (fun n : ℕ => IsUnit (n : ZMod q)), ‖a n‖ ^ 2 := by
  rw [dirichlet_parseval_residue_classes]; set I : Finset ℕ := Finset.Ico M (M + N)
  set C : ℝ := (Nat.totient q : ℝ) + ((Nat.totient q : ℝ) / (q : ℝ)) * (N : ℝ)
  have h1 : (Nat.totient q : ℝ) * ∑ r : (ZMod q)ˣ, ‖∑ n ∈ I.filter (fun n : ℕ => (n : ZMod q) = (r : ZMod q)), a n‖ ^ 2 ≤
      C * ∑ r : (ZMod q)ˣ, ∑ n ∈ I.filter (fun n : ℕ => (n : ZMod q) = (r : ZMod q)), ‖a n‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]; refine Finset.sum_le_sum fun r _ => ?_
    calc (Nat.totient q : ℝ) * ‖∑ n ∈ I.filter (fun n : ℕ => (n : ZMod q) = (r : ZMod q)), a n‖ ^ 2
        ≤ ((Nat.totient q : ℝ) * ((I.filter (fun n : ℕ => (n : ZMod q) = (r : ZMod q))).card : ℝ)) *
            ∑ n ∈ I.filter (fun n : ℕ => (n : ZMod q) = (r : ZMod q)), ‖a n‖ ^ 2 := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (cauchy_schwarz_complex_card _ a) (Nat.cast_nonneg _)
      _ ≤ C * ∑ n ∈ I.filter (fun n : ℕ => (n : ZMod q) = (r : ZMod q)), ‖a n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (card_filter_zmod_Ico_le (q := q) M N (r : ZMod q)).2 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  refine h1.trans_eq ?_; congr 1; simp_rw [Finset.sum_filter]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hu : IsUnit (n : ZMod q)
  · obtain ⟨r₀, hr₀⟩ := hu; rw [if_pos ⟨r₀, hr₀⟩, Finset.sum_eq_single r₀]
    · rw [if_pos hr₀.symm]
    · intro r _ hne; exact if_neg fun h => hne (Units.ext (h.symm.trans hr₀.symm))
    · intro hm; exact absurd (Finset.mem_univ r₀) hm
  · rw [if_neg hu]; exact Finset.sum_eq_zero fun r _ => if_neg fun (h : (n : ZMod q) = (r : ZMod q)) => hu (h ▸ r.isUnit)

/-- Montgomery–Vaughan / Gallagher multiplicative mean-square inequality on `Ico M (M + N)`. -/
theorem dirichlet_mean_square_Ico_le {q : ℕ} [NeZero q] (M N : ℕ) (a : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Ico M (M + N), a n * χ (n : ZMod q)‖ ^ 2 ≤
      ((Nat.totient q : ℝ) + (N : ℝ)) * ∑ n ∈ Finset.Ico M (M + N), ‖a n‖ ^ 2 := by
  have htot : (Nat.totient q : ℝ) / (q : ℝ) ≤ 1 :=
    (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q)))).2 (by exact_mod_cast Nat.totient_le q)
  exact (dirichlet_mean_square_Ico_sharp (q := q) M N a).trans <|
    mul_le_mul (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)

/-- Exact character Parseval equality and Montgomery–Vaughan mean-square bound on `Icc 1 N`:
`∑_{χ mod q} ‖∑_{n ≤ N} a_n χ(n)‖² = φ(q) ∑_{r ∈ (ZMod q)ˣ} ‖∑_{n ≡ r} a_n‖² ≤ (φ(q) + N) ∑ ‖a_n‖²`. -/
theorem dirichlet_mean_square_Icc {q : ℕ} [NeZero q] (N : ℕ) (a : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q)‖ ^ 2 =
      (Nat.totient q : ℝ) * ∑ r : (ZMod q)ˣ, ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => (n : ZMod q) = (r : ZMod q)), a n‖ ^ 2 ∧
    (Nat.totient q : ℝ) * ∑ r : (ZMod q)ˣ, ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => (n : ZMod q) = (r : ZMod q)), a n‖ ^ 2 ≤
      ((Nat.totient q : ℝ) + (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have heq : Finset.Icc 1 N = Finset.Ico 1 (1 + N) := by ext n; simp only [mem_Icc, mem_Ico]; omega
  have hp := dirichlet_parseval_residue_classes (q := q) (Finset.Icc 1 N) a
  exact ⟨hp, by rw [← hp, heq]; exact dirichlet_mean_square_Ico_le (q := q) 1 N a⟩

open Classical in
/-- Subgroup restriction of the multiplicative mean-square bound (e.g. `Level.ofSub Ξ`). -/
theorem subgroup_dirichlet_mean_square_Icc_le {q : ℕ} [NeZero q]
    (Ξ : Subgroup (DirichletCharacter ℂ q)) (N : ℕ) (a : ℕ → ℂ) :
    ∑ χ : Ξ, ‖∑ n ∈ Finset.Icc 1 N, a n * (χ : DirichletCharacter ℂ q) (n : ZMod q)‖ ^ 2 ≤
      ((Nat.totient q : ℝ) + (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have hsub : ∑ χ : Ξ, ‖∑ n ∈ Finset.Icc 1 N, a n * (χ : DirichletCharacter ℂ q) (n : ZMod q)‖ ^ 2 ≤
      ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q)‖ ^ 2 :=
    (Finset.sum_map (Finset.univ : Finset Ξ) ⟨Subtype.val, Subtype.val_injective⟩
      (fun χ => ‖∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q)‖ ^ 2)).symm.le.trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _)
  have hfull := dirichlet_mean_square_Icc (q := q) N a
  exact hsub.trans (hfull.1.le.trans hfull.2)

private lemma card_dirichlet_univ_eq {q : ℕ} [NeZero q] :
    ((Finset.univ : Finset (DirichletCharacter ℂ q)).card : ℝ) = (Nat.totient q : ℝ) := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]

/-- Bridge into `RHDirect.ZeroDensityWindow.chebyshev_bad_card`. -/
theorem bad_dirichlet_chars_card_le {q : ℕ} [NeZero q] (N : ℕ) (a : ℕ → ℂ)
    (B : Finset (DirichletCharacter ℂ q)) {T : ℝ} (hT : 0 < T)
    (hBad : ∀ χ ∈ B, T ≤ ‖∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q)‖) :
    (B.card : ℝ) ≤ (((Nat.totient q : ℝ) + (N : ℝ)) / T ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  classical
  have htot : (0 : ℝ) < (Nat.totient q : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q)))
  set M : ℝ := (((Nat.totient q : ℝ) + (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) / (Nat.totient q : ℝ)
  have hcheb := ZeroDensityWindow.chebyshev_bad_card (Finset.subset_univ B)
    (fun χ => ‖∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q)‖) hT
    (by
      rw [show M * ((Finset.univ : Finset (DirichletCharacter ℂ q)).card : ℝ) = ((Nat.totient q : ℝ) + (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 by
        dsimp only [M]; rw [card_dirichlet_univ_eq, div_mul_cancel₀ _ htot.ne']]
      have hfull := dirichlet_mean_square_Icc (q := q) N a; exact hfull.1.le.trans hfull.2)
    (fun χ hχ => by rw [abs_of_nonneg (norm_nonneg _)]; exact hBad χ hχ)
  refine hcheb.trans_eq ?_; dsimp only [M]; rw [card_dirichlet_univ_eq]; field_simp [htot.ne', hT.ne']

/-- Bridge into `RHDirect.ZeroDensityWindow.share_of_bad`. -/
theorem good_dirichlet_chars_share {q : ℕ} [NeZero q] (N : ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    ∃ G : Finset (DirichletCharacter ℂ q),
      (Nat.totient q : ℝ) - (((Nat.totient q : ℝ) + (N : ℝ)) / T ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 ≤ (G.card : ℝ) ∧
      ∀ χ ∈ G, ‖∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q)‖ < T := by
  classical
  have htot : (0 : ℝ) < (Nat.totient q : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q)))
  set η : ℝ := ((((Nat.totient q : ℝ) + (N : ℝ)) / T ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) / (Nat.totient q : ℝ)
  obtain ⟨G, -, hGc, hG⟩ := ZeroDensityWindow.share_of_bad (Finset.univ : Finset (DirichletCharacter ℂ q))
    (η := η) (fun χ => ‖∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q)‖ < T)
    (fun B _ hB => by
      rw [show η * ((Finset.univ : Finset (DirichletCharacter ℂ q)).card : ℝ) = (((Nat.totient q : ℝ) + (N : ℝ)) / T ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 by
        dsimp only [η]; rw [card_dirichlet_univ_eq, div_mul_cancel₀ _ htot.ne']]
      exact bad_dirichlet_chars_card_le (q := q) N a B hT (fun χ hχ => not_lt.mp (hB χ hχ)))
  refine ⟨G, ?_, hG⟩
  rw [show (Nat.totient q : ℝ) - (((Nat.totient q : ℝ) + (N : ℝ)) / T ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 =
      (1 - η) * ((Finset.univ : Finset (DirichletCharacter ℂ q)).card : ℝ) by dsimp only [η]; rw [card_dirichlet_univ_eq, sub_mul, one_mul, div_mul_cancel₀ _ htot.ne']]
  exact hGc

end DirichletMeanSquare

/-! ## 3. Behrend Sphere-Convexity & 3-Term AP-Free Packing Theorem -/

section BehrendPacking

/-- `A` contains no nontrivial 3-term arithmetic progression. -/
def IsThreeAPFree (A : Finset ℕ) : Prop := ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a + c = 2 * b → a = b ∧ b = c
def sqNormR {d : ℕ} (x : Fin d → ℝ) : ℝ := ∑ i : Fin d, (x i) ^ 2
def sqNormN {d : ℕ} (x : Fin d → ℕ) : ℕ := ∑ i : Fin d, (x i) ^ 2

/-- Exact midpoint squared-norm identity: `x + z = 2 y → 2 ‖x‖² + 2 ‖z‖² = 4 ‖y‖² + ‖x - z‖²`. -/
theorem midpoint_sqNorm_identity {d : ℕ} {x y z : Fin d → ℝ} (hmid : ∀ i : Fin d, x i + z i = 2 * y i) :
    2 * sqNormR x + 2 * sqNormR z = 4 * sqNormR y + ∑ i : Fin d, (x i - z i) ^ 2 := by
  unfold sqNormR; rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by linear_combination (x i + z i + 2 * y i) * hmid i

/-- Strict convexity of the Euclidean sphere `‖x‖² = R` in `ℝ^d`: no nontrivial 3-term AP. -/
theorem sphere_no_three_ap_real {d : ℕ} {R : ℝ} {x y z : Fin d → ℝ}
    (hx : sqNormR x = R) (hy : sqNormR y = R) (hz : sqNormR z = R)
    (hmid : ∀ i : Fin d, x i + z i = 2 * y i) : x = y ∧ y = z := by
  have hsum0 : ∑ i : Fin d, (x i - z i) ^ 2 = 0 := by linarith [midpoint_sqNorm_identity hmid]
  have hxz : ∀ i : Fin d, x i = z i := fun i => by
    linarith [sq_eq_zero_iff.1 ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j - z j))).1 hsum0 i (Finset.mem_univ i))]
  exact ⟨funext fun i => by linarith [hmid i, hxz i], funext fun i => by linarith [hmid i, hxz i]⟩

/-- Lattice sphere convexity in `ℕ^d`: no nontrivial 3-term AP on `sqNormN x = R`. -/
theorem sphere_no_three_ap_nat {d R : ℕ} {x y z : Fin d → ℕ}
    (hx : sqNormN x = R) (hy : sqNormN y = R) (hz : sqNormN z = R)
    (hmid : ∀ i : Fin d, x i + z i = 2 * y i) : x = y ∧ y = z := by
  have hr := sphere_no_three_ap_real (R := (R : ℝ))
    (x := fun i => (x i : ℝ)) (y := fun i => (y i : ℝ)) (z := fun i => (z i : ℝ))
    (by dsimp only [sqNormR]; unfold sqNormN at hx; exact_mod_cast hx)
    (by dsimp only [sqNormR]; unfold sqNormN at hy; exact_mod_cast hy)
    (by dsimp only [sqNormR]; unfold sqNormN at hz; exact_mod_cast hz) (fun i => by exact_mod_cast hmid i)
  exact ⟨funext fun i => Nat.cast_injective (congrFun hr.1 i), funext fun i => Nat.cast_injective (congrFun hr.2 i)⟩

/-- Base-`B` digit encoding `∑ i : Fin d, x_i * B^i`. -/
def behrendEncode {d : ℕ} (B : ℕ) (x : Fin d → ℕ) : ℕ := ∑ i : Fin d, x i * B ^ (i : ℕ)

private lemma behrendEncode_succ {d : ℕ} (B : ℕ) (x : Fin (d + 1) → ℕ) :
    behrendEncode B x = x 0 + B * behrendEncode B (fun i => x i.succ) := by
  unfold behrendEncode; rw [Fin.sum_univ_succ, Finset.mul_sum]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ']
  congr 1; exact Finset.sum_congr rfl fun i _ => by ring

/-- Range bound: `x_i < B` implies `behrendEncode B x < B^d`. -/
theorem behrendEncode_lt : ∀ {d : ℕ} {B : ℕ} (x : Fin d → ℕ), 0 < B → (∀ i, x i < B) → behrendEncode B x < B ^ d
  | 0, _, _, _, _ => by simp [behrendEncode]
  | d + 1, B, x, hB, hx => by
    rw [behrendEncode_succ, pow_succ']
    have ih := behrendEncode_lt (fun i : Fin d => x i.succ) hB (fun i => hx i.succ); have h0 := hx 0; nlinarith

/-- Uniqueness of base-`B` digit representation when all digits are `< B`. -/
theorem behrendEncode_injective : ∀ {d : ℕ} {B : ℕ} {u v : Fin d → ℕ},
    (∀ i, u i < B) → (∀ i, v i < B) → behrendEncode B u = behrendEncode B v → u = v
  | 0, _, _, _, _, _, _ => funext fun i => Fin.elim0 i
  | d + 1, B, u, v, hu, hv, heq => by
    rw [behrendEncode_succ, behrendEncode_succ] at heq
    have hB : 0 < B := Nat.pos_of_ne_zero fun h0 => by have := hu 0; omega
    have hmod := congrArg (· % B) heq
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hu 0), Nat.mod_eq_of_lt (hv 0)] at hmod
    have hdiv := congrArg (· / B) heq
    rw [Nat.add_mul_div_left _ _ hB, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (hu 0), Nat.div_eq_of_lt (hv 0), zero_add, zero_add] at hdiv
    have htail := behrendEncode_injective (fun i => hu i.succ) (fun i => hv i.succ) hdiv
    exact funext fun i => Fin.cases hmod (fun j => congrFun htail j) i

/-- Carry-free 3-AP preservation for base-`B` encoding (`2 * m ≤ B`). -/
theorem behrendEncode_three_ap_iff {d m B : ℕ} (hB : 2 * m ≤ B)
    {x y z : Fin d → ℕ} (hx : ∀ i, x i < m) (hy : ∀ i, y i < m) (hz : ∀ i, z i < m) :
    behrendEncode B x + behrendEncode B z = 2 * behrendEncode B y ↔ ∀ i : Fin d, x i + z i = 2 * y i := by
  have hadd : behrendEncode B x + behrendEncode B z = behrendEncode B (fun i => x i + z i) := by
    unfold behrendEncode; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => (add_mul _ _ _).symm
  have hmul : 2 * behrendEncode B y = behrendEncode B (fun i => 2 * y i) := by
    unfold behrendEncode; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
  rw [hadd, hmul]
  exact ⟨fun heq i => congrFun (behrendEncode_injective
      (fun j => lt_of_lt_of_le (by have := hx j; have := hz j; omega) hB)
      (fun j => lt_of_lt_of_le (by have := hy j; omega) hB) heq) i, fun h => congrArg _ (funext h)⟩

def gridBox (d m : ℕ) : Finset (Fin d → ℕ) := Fintype.piFinset fun _ : Fin d => Finset.range m
def sphereBox (d m R : ℕ) : Finset (Fin d → ℕ) := (gridBox d m).filter fun x => sqNormN x = R

/-- Pigeonhole sphere packing on `[0, m)^d`: `∃ R < d * m², m^d ≤ d * m² * |S_R|`. -/
theorem exists_behrend_sphere_pack {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    ∃ R : ℕ, R < d * m ^ 2 ∧ m ^ d ≤ d * m ^ 2 * (sphereBox d m R).card := by
  have hbox : (gridBox d m).card = m ^ d := by unfold gridBox; simp [Fintype.card_piFinset]
  have hm2 : 1 ≤ m ^ 2 := by nlinarith
  have hmaps : ∀ x ∈ gridBox d m, sqNormN x ∈ Finset.range (d * m ^ 2) := fun x hx => by
    rw [Finset.mem_range]
    have hle : ∀ i : Fin d, (x i) ^ 2 ≤ m ^ 2 - 1 := fun i => by
      have hi : x i < m := Finset.mem_range.1 (Fintype.mem_piFinset.1 hx i); have : (x i) ^ 2 < m ^ 2 := by nlinarith
      omega
    exact lt_of_le_of_lt ((Finset.sum_le_sum fun i _ => hle i).trans_eq (by simp))
      (Nat.mul_lt_mul_of_pos_left (by omega : m ^ 2 - 1 < m ^ 2) hd)
  have hsum : ∑ R ∈ Finset.range (d * m ^ 2), (sphereBox d m R).card = m ^ d := by
    rw [← hbox, Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to hmaps]
    exact Finset.sum_congr rfl fun R _ => Finset.card_eq_sum_ones _
  by_contra hnone; push Not at hnone
  have hlt := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 (by positivity : d * m ^ 2 ≠ 0))
    (fun R hR => hnone R (Finset.mem_range.1 hR))
  rw [← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_range, smul_eq_mul] at hlt; exact lt_irrefl _ hlt

/-- Constructive Behrend 3-AP-free packing in `Finset.range ((2 * m)^d)`. -/
theorem behrend_packing_finset {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    ∃ A : Finset ℕ, A ⊆ Finset.range ((2 * m) ^ d) ∧ IsThreeAPFree A ∧ m ^ d ≤ d * m ^ 2 * A.card := by
  obtain ⟨R, -, hcard⟩ := exists_behrend_sphere_pack hd hm; let S := sphereBox d m R
  have hxm : ∀ x ∈ S, ∀ i, x i < m := fun x hx i => Finset.mem_range.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1 i)
  have hinj : Set.InjOn (behrendEncode (2 * m)) (S : Set (Fin d → ℕ)) := fun x hx y hy hxy =>
    behrendEncode_injective (fun i => lt_trans (hxm x hx i) (by omega)) (fun i => lt_trans (hxm y hy i) (by omega)) hxy
  refine ⟨S.image (behrendEncode (2 * m)), ?_, ?_, by rwa [Finset.card_image_of_injOn hinj]⟩
  · intro a ha; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    exact Finset.mem_range.2 (behrendEncode_lt x (by omega) fun i => lt_trans (hxm x hx i) (by omega))
  · intro a ha b hb c hc hap
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha; obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hc
    have ⟨hxy, hyz⟩ := sphere_no_three_ap_nat (Finset.mem_filter.1 hx).2 (Finset.mem_filter.1 hy).2
      (Finset.mem_filter.1 hz).2 ((behrendEncode_three_ap_iff (le_refl (2 * m)) (hxm x hx) (hxm y hy) (hxm z hz)).1 hap)
    exact ⟨congrArg _ hxy, congrArg _ hyz⟩

/-- Quantitative Behrend (1946) subexponential lower bound:
for every `N ≥ 64`, there exists a 3-AP-free `A ⊆ Finset.range N` with `N * exp(-6 √(log N)) ≤ |A|`. -/
theorem behrend_subexponential_bound {N : ℕ} (hN : 64 ≤ N) :
    ∃ A : Finset ℕ, A ⊆ Finset.range N ∧ IsThreeAPFree A ∧
      (N : ℝ) * Real.exp (-6 * Real.sqrt (Real.log (N : ℝ))) ≤ (A.card : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set L : ℝ := Real.log (N : ℝ); have hl2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2_lo : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2_hi : Real.log 2 < (7 : ℝ) / 10 := by linarith [Real.log_two_lt_d9]
  have hL6 : 6 * Real.log 2 ≤ L := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 64) (by exact_mod_cast hN : (64 : ℝ) ≤ N)
    rw [show (64 : ℝ) = (2 : ℝ) ^ (6 : ℕ) by norm_num, Real.log_pow] at h; push_cast at h; linarith
  have hLpos : 0 < L := by linarith
  set u : ℝ := Real.sqrt (L / Real.log 2); have hu2 : u ^ 2 = L / Real.log 2 := Real.sq_sqrt (div_nonneg hLpos.le hl2_pos.le)
  have hLeq : L = u ^ 2 * Real.log 2 := by rw [hu2, div_mul_cancel₀ _ hl2_pos.ne']
  have hu_ge2 : 2 ≤ u := (Real.le_sqrt (by norm_num) (div_nonneg hLpos.le hl2_pos.le)).2 <| (le_div_iff₀ hl2_pos).2 (by linarith)
  set d : ℕ := ⌊u⌋₊; have hd_ge2 : 2 ≤ d := Nat.le_floor hu_ge2
  have hd_posR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd_le_u : (d : ℝ) ≤ u := Nat.floor_le (by linarith); have hu_half : u / 2 ≤ (d : ℝ) := by linarith [Nat.lt_floor_add_one u]
  set r : ℝ := (N : ℝ) ^ (1 / (d : ℝ)); have hr_pos : 0 < r := Real.rpow_pos_of_pos hNpos _
  have hlogr : Real.log r = L / (d : ℝ) := by dsimp only [r]; rw [Real.log_rpow hNpos]; ring
  have hrpow : r ^ d = (N : ℝ) := by dsimp only [r]; rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, one_div_mul_cancel hd_posR.ne', Real.rpow_one]
  have hr_ge4 : 4 ≤ r := (Real.log_le_log_iff (by norm_num) hr_pos).1 <| by
    rw [hlogr, show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast
    have : u * Real.log 2 ≤ L / (d : ℝ) := (le_div_iff₀ hd_posR).2 (by rw [hLeq]; nlinarith); nlinarith
  set m : ℕ := ⌊r / 2⌋₊; have hm_ge2 : 2 ≤ m := Nat.le_floor (by linarith)
  have hm_le : (m : ℝ) ≤ r / 2 := Nat.floor_le (by linarith); have hm_ge : r / 4 ≤ (m : ℝ) := by linarith [Nat.lt_floor_add_one (r / 2)]
  have h2m_pow : (2 * m) ^ d ≤ N := by
    have h2 : (((2 * m) ^ d : ℕ) : ℝ) ≤ r ^ d := by push_cast; exact pow_le_pow_left₀ (by positivity) (by linarith : (2 : ℝ) * m ≤ r) d
    rw [hrpow] at h2; exact_mod_cast h2
  obtain ⟨A, hAsub, hAfree, hAcard⟩ := behrend_packing_finset (by omega : 0 < d) (by omega : 0 < m)
  refine ⟨A, hAsub.trans (Finset.range_mono h2m_pow), hAfree, ?_⟩
  have hAcardR : (m : ℝ) ^ d ≤ (d : ℝ) * (m : ℝ) ^ 2 * (A.card : ℝ) := by exact_mod_cast hAcard
  have hmd_ge : (N : ℝ) / (4 : ℝ) ^ d ≤ (m : ℝ) ^ d := by simpa [div_pow, hrpow] using pow_le_pow_left₀ (by positivity) hm_ge d
  have hden_le : (4 : ℝ) ^ d * ((d : ℝ) * (m : ℝ) ^ 2) ≤ Real.exp (6 * Real.sqrt L) := by
    have hdm2 : (d : ℝ) * (m : ℝ) ^ 2 ≤ ((d : ℝ) / 4) * r ^ 2 := by have := pow_le_pow_left₀ (Nat.cast_nonneg _) hm_le 2; nlinarith
    have hd_exp : (d : ℝ) / 4 ≤ Real.exp ((d : ℝ) * Real.log 2) := by have := Real.add_one_le_exp ((d : ℝ) * Real.log 2); nlinarith
    have h4d : (4 : ℝ) ^ d = Real.exp (2 * (d : ℝ) * Real.log 2) := by
      rw [show (4 : ℝ) = Real.exp (2 * Real.log 2) by rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num)]; norm_num, ← Real.exp_nat_mul]
      congr 1; ring
    have hr2 : r ^ 2 = Real.exp (2 * L / (d : ℝ)) := by rw [← Real.exp_log (pow_pos hr_pos 2), Real.log_pow, hlogr]; congr 1; ring
    have hprod : (4 : ℝ) ^ d * ((d : ℝ) * (m : ℝ) ^ 2) ≤ Real.exp ((d : ℝ) * Real.log 2 + 2 * (d : ℝ) * Real.log 2 + 2 * L / (d : ℝ)) := by
      calc (4 : ℝ) ^ d * ((d : ℝ) * (m : ℝ) ^ 2) ≤ ((d : ℝ) / 4) * (4 : ℝ) ^ d * r ^ 2 := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) d]
        _ ≤ Real.exp ((d : ℝ) * Real.log 2) * Real.exp (2 * (d : ℝ) * Real.log 2) * Real.exp (2 * L / (d : ℝ)) := by rw [h4d, hr2]; gcongr
        _ = Real.exp ((d : ℝ) * Real.log 2 + 2 * (d : ℝ) * Real.log 2 + 2 * L / (d : ℝ)) := by rw [← Real.exp_add, ← Real.exp_add]
    refine hprod.trans (Real.exp_le_exp.2 ?_)
    have hsqp : u * Real.log 2 = Real.sqrt (L * Real.log 2) :=
      ((Real.sqrt_eq_iff_mul_self_eq (mul_nonneg hLpos.le hl2_pos.le) (by positivity)).2 (by rw [hLeq]; ring)).symm
    have ht1 : (d : ℝ) * Real.log 2 ≤ Real.sqrt (L * Real.log 2) := hsqp ▸ mul_le_mul_of_nonneg_right hd_le_u hl2_pos.le
    have ht2 : 2 * L / (d : ℝ) ≤ 4 * Real.sqrt (L * Real.log 2) := (div_le_iff₀ hd_posR).2 (by rw [← hsqp, hLeq]; nlinarith)
    have h7 : 7 * Real.sqrt (L * Real.log 2) ≤ 6 * Real.sqrt L := by
      have hsq : (7 * Real.sqrt (L * Real.log 2)) ^ 2 ≤ (6 * Real.sqrt L) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hLpos.le hl2_pos.le), Real.sq_sqrt hLpos.le]; nlinarith
      nlinarith [Real.sqrt_nonneg (L * Real.log 2), Real.sqrt_nonneg L]
    linarith
  have hcomb : (N : ℝ) ≤ Real.exp (6 * Real.sqrt L) * (A.card : ℝ) := by
    have h4pos : (0 : ℝ) < (4 : ℝ) ^ d := by positivity
    have h1 := mul_le_mul_of_nonneg_left (hmd_ge.trans hAcardR) h4pos.le
    rw [mul_div_cancel₀ _ h4pos.ne', ← mul_assoc] at h1; exact h1.trans (mul_le_mul_of_nonneg_right hden_le (Nat.cast_nonneg _))
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _), mul_comm]; exact hcomb

/-- Corollary: for every `ε > 0`, all sufficiently large `N` admit a 3-AP-free `A ⊆ range N` with `N^(1 - ε) ≤ |A|`. -/
theorem behrend_density_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ A : Finset ℕ, A ⊆ Finset.range N ∧ IsThreeAPFree A ∧ (N : ℝ) ^ (1 - ε) ≤ (A.card : ℝ) := by
  refine ⟨max 64 ⌈Real.exp (36 / ε ^ 2)⌉₊, fun N hN => ?_⟩
  obtain ⟨A, hsub, hfree, hcard⟩ := behrend_subexponential_bound (le_trans (le_max_left _ _) hN)
  refine ⟨A, hsub, hfree, ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by have : 64 ≤ N := le_trans (le_max_left _ _) hN; exact_mod_cast (by omega : 0 < N)
  have hNexp : Real.exp (36 / ε ^ 2) ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (le_trans (le_max_right 64 _) hN))
  have hlog : 36 / ε ^ 2 ≤ Real.log (N : ℝ) := by have h := Real.log_le_log (Real.exp_pos _) hNexp; rwa [Real.log_exp] at h
  have hL0 : 0 ≤ Real.log (N : ℝ) := le_trans (by positivity) hlog
  have h6 : 6 * Real.sqrt (Real.log (N : ℝ)) ≤ ε * Real.log (N : ℝ) := by
    have hmul : 36 ≤ Real.log (N : ℝ) * ε ^ 2 := (div_le_iff₀ (sq_pos_of_pos hε)).1 hlog
    have hsq : (6 * Real.sqrt (Real.log (N : ℝ))) ^ 2 ≤ (ε * Real.log (N : ℝ)) ^ 2 := by rw [mul_pow, mul_pow, Real.sq_sqrt hL0]; nlinarith
    nlinarith [Real.sqrt_nonneg (Real.log (N : ℝ)), mul_nonneg hε.le hL0]
  rw [show (N : ℝ) ^ (1 - ε) = (N : ℝ) * Real.exp (-ε * Real.log (N : ℝ)) by
    rw [Real.rpow_sub hNpos, Real.rpow_one, Real.rpow_def_of_pos hNpos, neg_mul, Real.exp_neg, div_eq_mul_inv, mul_comm (Real.log (N : ℝ)) ε]]
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hNpos.le).trans hcard

end BehrendPacking
end Stage2BehrendSieve
end RHDirect

end
