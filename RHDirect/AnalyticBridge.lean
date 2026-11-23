import RHDirect.Interfaces
import RHDirect.LandauWindow
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# RHDirect.AnalyticBridge

Compact, direct, 0-`sorry`, 0-`axiom` Lean 4 rebuild of the Analytic Number Theory & Explicit
Formula Bridge connecting:

1. **Finite Abelian Fourier Inversion & `(3o + 1)` Coset Weight Clearing (`tops_sum`)**:
   Replaces `PrimitiveCosets/TopsSum.lean` and the redundant `toE`/`chr`/`ArithData` translation
   layers with direct Fourier inversion on `RHDirect.CosetFrame`, showing that `(4, 3)/(3o + 1)`
   coset equidistribution isolates nontrivial characters with weight `(3o + 1)⁻¹` and clears
   denominators in `(3o + 1) * L.Gm y`.
2. **Windowed Landau Deduction to `ZeroFreeAll` (`analyticBridgeContract`)**:
   Bridges `Level.Gm` to `CharFamily.Gm`, applies `RHDirect.zeroFree_of_rpow_window`, and proves
   `analyticBridgeContract : AnalyticBridgeContract` unconditionally (zero extra hypotheses!).
   Also includes `levelWindowBound_of_family_windows` (replacing `TotientGaloisClasses/TopWin.lean`).
3. **Direct Deduction of All 5 Headline RH/GRH Theorems**:
   Proves `ZeroFreeAll → DirichletLNonvanishingRightOfHalf → DirichletLZerosOnLine →
   PrimitiveDirichletLZerosOnLine` and `RiemannHypothesis` / `RiemannZetaZerosOnLine` via
   Euler-factor stripping, functional-equation reflection `s ↦ 1 - s`, and `ζ(s) = L(1, s)`.
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

noncomputable section

namespace RHDirect

/-! ## Part 1: Finite Abelian Fourier Inversion & `(3o + 1)` Weight Clearing (`TopsSum`) -/

private lemma coset_char_sum {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (A0 : AddSubgroup H) [DecidablePred (· ∈ A0)] (θ : AddChar H ℂ)
    (h0 : ∀ s ∈ A0, θ s = 1) (t : H) :
    ∑ g : H, (if t - g ∈ A0 then θ g else 0) = (Fintype.card A0 : ℂ) * θ t := by
  have step : ∀ g : H, (if t - g ∈ A0 then θ g else 0) = if t - g ∈ A0 then θ t else 0 := by
    intro g
    split_ifs with hg
    · have e : g = t + -(t - g) := by abel
      rw [e, AddChar.map_add_eq_mul, h0 _ (A0.neg_mem hg), mul_one]
    · rfl
  have eqv : A0 ≃ {g : H // t - g ∈ A0} :=
    { toFun := fun s => ⟨t - s, by simp [s.2]⟩
      invFun := fun g => ⟨t - g, g.2⟩
      left_inv := fun s => by ext; simp
      right_inv := fun g => by ext; simp }
  have hc : (Finset.univ.filter fun g : H => t - g ∈ A0).card = Fintype.card A0 := by
    rw [← Fintype.card_subtype, ← Fintype.card_congr eqv]
  rw [Finset.sum_congr rfl fun g _ => step g, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hc]

/-- General finite abelian Fourier discrepancy bound for coset-equidistributed subsets `TT ⊆ H`. -/
theorem tops_sum_gen {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (A0 : AddSubgroup H) [DecidablePred (· ∈ A0)] (θ : AddChar H ℂ)
    (h0 : ∀ s ∈ A0, θ s = 1) (h1 : θ ≠ 0) (TT : Finset H) (o : ℕ)
    (ho : o * Fintype.card A0 = Fintype.card H) (b c η : ℝ)
    (hs : ∀ g : H, |((TT.filter fun t => t - g ∈ A0).card : ℝ) -
      (b + if g ∈ A0 then c else 0)| ≤ η) :
    ‖(∑ t ∈ TT, θ t) - (c : ℂ)‖ ≤ (o : ℝ) * η := by
  have hiff : ∀ g : H, 0 - g ∈ A0 ↔ g ∈ A0 := fun g => by rw [zero_sub, neg_mem_iff]
  have hz := coset_char_sum A0 θ h0 0
  simp only [hiff, AddChar.map_zero_eq_one, mul_one] at hz
  have hB : ∑ g : H, θ g = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr h1
  have hC : ∑ g : H, θ g * (if g ∈ A0 then (c : ℂ) else 0) = (Fintype.card A0 : ℂ) * c := by
    rw [← hz, Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> ring
  have hA : ∑ g : H, θ g * ((TT.filter fun t => t - g ∈ A0).card : ℂ) =
      (Fintype.card A0 : ℂ) * ∑ t ∈ TT, θ t := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun t _ => (coset_char_sum A0 θ h0 t).symm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  let e : H → ℝ := fun g => ((TT.filter fun t => t - g ∈ A0).card : ℝ) - (b + if g ∈ A0 then c else 0)
  have key : (Fintype.card A0 : ℂ) * ((∑ t ∈ TT, θ t) - c) = ∑ g : H, θ g * ((e g : ℝ) : ℂ) := by
    have hsplit : ∀ g : H, θ g * ((e g : ℝ) : ℂ) = θ g * ((TT.filter fun t => t - g ∈ A0).card : ℂ)
        - (b : ℂ) * θ g - θ g * (if g ∈ A0 then (c : ℂ) else 0) := by
      intro g; simp only [e]; split_ifs <;> push_cast <;> ring
    rw [Finset.sum_congr rfl fun g _ => hsplit g, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      hA, ← Finset.mul_sum, hB, hC]
    ring
  have hnorm : ∀ g : H, ‖θ g‖ = 1 := by
    intro g
    have hp : θ g ^ Fintype.card H = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
    have hq : ‖θ g‖ ^ Fintype.card H = 1 := by rw [← norm_pow, hp, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).mp hq
  have hbound : ‖∑ g : H, θ g * ((e g : ℝ) : ℂ)‖ ≤ (Fintype.card H : ℝ) * η := by
    calc ‖∑ g : H, θ g * ((e g : ℝ) : ℂ)‖
        ≤ ∑ g : H, ‖θ g * ((e g : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _g : H, η := Finset.sum_le_sum fun g _ => by
          rw [norm_mul, hnorm, one_mul, Complex.norm_real, Real.norm_eq_abs]; exact hs g
      _ = (Fintype.card H : ℝ) * η := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (0 : ℝ) < Fintype.card A0 := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨(⟨0, A0.zero_mem⟩ : A0)⟩
  have h3 : (Fintype.card A0 : ℝ) * ‖(∑ t ∈ TT, θ t) - (c : ℂ)‖ ≤ (Fintype.card A0 : ℝ) * ((o : ℝ) * η) := by
    calc (Fintype.card A0 : ℝ) * ‖(∑ t ∈ TT, θ t) - (c : ℂ)‖
        = ‖(Fintype.card A0 : ℂ) * ((∑ t ∈ TT, θ t) - c)‖ := by rw [norm_mul, Complex.norm_natCast]
      _ = ‖∑ g : H, θ g * ((e g : ℝ) : ℂ)‖ := by rw [key]
      _ ≤ (Fintype.card H : ℝ) * η := hbound
      _ = (Fintype.card A0 : ℝ) * ((o : ℝ) * η) := by rw [← ho]; push_cast; ring
  exact le_of_mul_le_mul_left h3 hn

/-- **Coset Fourier Inversion (`TopsSum`) on `CosetFrame`**:
If `TT ⊆ φ.A` satisfies the `(4, 3)/(3o + 1)` coset share condition `φ.Shares TT δ`, then every
nontrivial additive character `θ : AddChar φ.A ℂ` trivial on `φ.A0` has sum
`∑_{t ∈ TT} θ(t) = (3o + 1)⁻¹ |TT| + O(o δ |TT|)`. -/
theorem tops_sum (φ : CosetFrame) (TT : Finset φ.A) (δ : ℝ) (hsh : φ.Shares TT δ)
    (θ : AddChar φ.A ℂ) (h0 : ∀ s ∈ φ.A0, θ s = 1) (hnt : θ ≠ 0) :
    ‖(∑ t ∈ TT, θ t) - (((3 * (φ.o : ℝ) + 1)⁻¹ : ℝ) : ℂ) * (TT.card : ℂ)‖ ≤
      (φ.o : ℝ) * δ * (TT.card : ℝ) := by
  have hpos : (0 : ℝ) < 3 * (φ.o : ℝ) + 1 := by positivity
  have hs : ∀ g : φ.A, |((TT.filter fun t => t - g ∈ φ.A0).card : ℝ) -
      (3 * (3 * (φ.o : ℝ) + 1)⁻¹ * (TT.card : ℝ) +
        if g ∈ φ.A0 then (3 * (φ.o : ℝ) + 1)⁻¹ * (TT.card : ℝ) else 0)| ≤ δ * (TT.card : ℝ) := by
    intro g
    have hg := hsh g
    convert hg using 3
    simp only [CosetFrame.lam]
    split_ifs <;> field_simp <;> ring
  have hfin := tops_sum_gen φ.A0 θ h0 hnt TT φ.o φ.index_eq
    (3 * (3 * (φ.o : ℝ) + 1)⁻¹ * (TT.card : ℝ)) ((3 * (φ.o : ℝ) + 1)⁻¹ * (TT.card : ℝ))
    (δ * (TT.card : ℝ)) hs
  push_cast at hfin ⊢
  exact le_of_le_of_eq hfin (by ring)

/-- Exact probability normalization of `CosetFrame.lam`: `4/(3o+1) + (o-1)·3/(3o+1) = 1`. -/
theorem cosetFrame_lam_total (φ : CosetFrame) :
    φ.lam 0 + ((φ.o : ℝ) - 1) * (3 / (3 * (φ.o : ℝ) + 1)) = 1 := by
  have hpos : (3 * (φ.o : ℝ) + 1) ≠ 0 := by positivity
  simp only [CosetFrame.lam, φ.A0.zero_mem, ite_true]
  field_simp
  ring

/-- Clearing the `(3o + 1)⁻¹` denominator in `Level.Gm` produces positive integer weights. -/
theorem level_gm_clear_denom (L : Level) (y : ℝ) :
    (3 * (L.o : ℝ) + 1) * L.Gm y =
      (3 * (L.o : ℝ) + 1) * Gz y + ∑ ψ ∈ L.Nt, (Gchi ψ.χ y).re := by
  have hpos : (3 * (L.o : ℝ) + 1) ≠ 0 := by positivity
  simp only [Level.Gm, Level.wt, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [← mul_assoc, mul_inv_cancel₀ hpos, one_mul]

/-! ## Part 2: `Level` → `CharFamily` & Windowed Landau Nonvanishing (`AnalyticBridgeContract`) -/

private lemma Gchi_one_re_eq_Gz (y : ℝ) : (Gchi PChar.one.χ y).re = Gz y := by
  have h1 : PChar.one.χ = 1 := rfl
  have hval : (fun n : ℕ => PChar.one.χ n) = fun _ => (1 : ℂ) := by
    funext n
    change (1 : DirichletCharacter ℂ 1) n = 1
    exact MulChar.one_apply (isUnit_of_subsingleton _)
  simp only [Gchi, if_pos h1, hval, Gz, Complex.add_re, Complex.sub_re, Complex.ofReal_re]

open Classical in
/-- Canonical `CharFamily` associated to a `Level`, unifying `Level.Gm` and `CharFamily.Gm`
without any intermediate translation structs. -/
def levelToCharFamily (L : Level) : CharFamily where
  ι := L.KEPT
  N := fun i => i.1.N
  nz := fun i => i.1.ne
  χ := fun i => i.1.χ
  a := fun i => if i.1 = PChar.one then 1 else L.wt i.1
  a_pos := fun i => by
    split_ifs
    · exact one_pos
    · simp only [Level.wt]; positivity
  adm := fun i => by
    by_cases h : i.1.χ = 1
    · left
      have hp : i.1.χ.conductor = i.1.N := i.1.prim
      rw [h, DirichletCharacter.conductor_one] at hp
      exact hp.symm
    · exact Or.inr h

theorem levelToCharFamily_Gm (L : Level) (y : ℝ) :
    (levelToCharFamily L).Gm y = L.Gm y := by
  classical
  change ∑ i : L.KEPT, (if i.1 = PChar.one then 1 else L.wt i.1) * (Gchi i.1.χ y).re = L.Gm y
  rw [Finset.sum_coe_sort L.KEPT (fun ψ => (if ψ = PChar.one then 1 else L.wt ψ) * (Gchi ψ.χ y).re)]
  rw [← Finset.add_sum_erase _ _ L.one_mem, Level.Gm, Level.Nt]
  congr 1
  · simp [Gchi_one_re_eq_Gz]
  · refine Finset.sum_congr rfl fun ψ hψ => ?_
    simp [Finset.ne_of_mem_erase hψ]

theorem levelToCharFamily_zeroFree_iff (L : Level) (θ : ℝ) :
    (levelToCharFamily L).ZeroFree θ ↔ L.ZeroFreeAbove θ := by
  constructor
  · intro h ψ hψ s hs
    exact h ⟨ψ, hψ⟩ s hs
  · intro h i s hs
    exact h i.1 i.2 s hs

/-- Windowed nonvanishing for any `Level` from a single `HasRpowWindow L.Gm θ (la - 1) 1` bound. -/
theorem level_zeroFreeAbove_of_rpow_window (L : Level) {la θ : ℝ} (hla : 1 < la)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hW : HasRpowWindow L.Gm θ (la - 1) 1) :
    L.ZeroFreeAbove θ := by
  rw [← levelToCharFamily_zeroFree_iff]
  refine zeroFree_of_rpow_window (levelToCharFamily L) (δ := la - 1) (C := 1)
    hθ0 hθ1 (by linarith) fun Y₀ => ?_
  obtain ⟨Y, hY, hy⟩ := hW Y₀
  refine ⟨Y, hY, fun y hy' => ?_⟩
  rw [levelToCharFamily_Gm]
  exact hy y hy'

/-- `LevelWindowBound L la` (`la > 1`) implies `L.ZeroFreeLevel` (`Re(s) > 1/2`). -/
theorem level_zeroFreeLevel_of_windowBound (L : Level) {la : ℝ} (hla : 1 < la)
    (hW : LevelWindowBound L la) : L.ZeroFreeLevel := by
  intro ψ hψ s hs
  set δ := min (s.re - 1 / 2) (1 / 2)
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ s.re - 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ 1 / 2 := min_le_right _ _
  set θ := 1 / 2 + δ / 2 with hθ_def
  have hθ0 : 0 < θ := by rw [hθ_def]; linarith
  have hθ_half : 1 / 2 < θ := by rw [hθ_def]; linarith
  have hθ1 : θ < 1 := by rw [hθ_def]; linarith
  exact level_zeroFreeAbove_of_rpow_window L hla hθ0 hθ1 (hW θ hθ_half hθ1) ψ hψ s
    (by rw [hθ_def]; linarith)

/-- Helper matching `TotientGaloisClasses/TopWin.lean`: if for every small `ε > 0` there is a
windowed set `W` (`HasWindows W la`) on which `L.Gm y ≤ y ^ (1/2 + C * ε)` for large `y`, then
`LevelWindowBound L la` holds. -/
theorem levelWindowBound_of_family_windows (L : Level) {la C ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (h : ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ (W : Set ℝ) (x₁ : ℝ),
      HasWindows W la ∧ ∀ y ≥ x₁, y ∈ W → L.Gm y ≤ y ^ ((1 : ℝ) / 2 + C * ε)) :
    LevelWindowBound L la := by
  intro θ hθ_half _hθ1 Y₀
  have hδ : 0 < θ - 1 / 2 := by linarith
  have hp : 0 < |C| + 1 := by positivity
  set ε : ℝ := min (ε₁ / 2) ((θ - 1 / 2) / (|C| + 1)) with hε_def
  have hε0 : 0 < ε := lt_min (by linarith) (div_pos hδ hp)
  have hεlt : ε < ε₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hCε : C * ε ≤ θ - 1 / 2 := by
    have a1 := mul_le_mul_of_nonneg_right (le_abs_self C) hε0.le
    have a2 : ε ≤ (θ - 1 / 2) / (|C| + 1) := min_le_right _ _
    rw [le_div_iff₀ hp] at a2
    nlinarith
  obtain ⟨W, x₁, hWin, hbd⟩ := h ε hε0 hεlt
  obtain ⟨Y, hY, hsub⟩ := hWin (max Y₀ (max x₁ 1))
  refine ⟨Y, (le_max_left _ _).trans hY, fun y hy => ?_⟩
  have hYx1 : x₁ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hY1 : 1 ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans hY)
  have hy_sub : y ∈ Set.Icc Y (Y ^ la) := by
    have : 1 + (la - 1) = la := by ring
    rwa [this] at hy
  rw [one_mul]
  exact (hbd y (hYx1.trans hy_sub.1) (hsub hy_sub)).trans
    (Real.rpow_le_rpow_of_exponent_le (hY1.trans hy_sub.1) (by linarith))

/-- `AllLevelsWindowBound la` (`la > 1`) implies `ZeroFreeAll` (`L(ψ, s) ≠ 0` for all primitive
Dirichlet characters `ψ` and all `Re(s) > 1/2`). -/
theorem zeroFreeAll_of_allLevelsWindowBound {la : ℝ} (hla : 1 < la)
    (hW : AllLevelsWindowBound la) : ZeroFreeAll := by
  intro ψ
  exact level_zeroFreeLevel_of_windowBound (Level.cyc ψ) hla (hW ψ) ψ (Level.mem_cyc ψ)

/-- **Pillar 1 (`AnalyticBridgeContract`) — proved unconditionally from Mathlib `v4.33.1`**
(zero extra assumptions, zero `sorry`, zero custom `axiom`s). -/
theorem analyticBridgeContract : AnalyticBridgeContract where
  zeroFreeAll_of_windows := fun _la hla hW => zeroFreeAll_of_allLevelsWindowBound hla hW

/-! ## Part 3: Direct Deduction of All 5 Headline RH/GRH Theorems -/

private lemma euler_factor_ne_zero {M : ℕ} (ψ : DirichletCharacter ℂ M) {s : ℂ} (hs : 0 < s.re)
    (p : ℕ) (hp : p.Prime) : (1 : ℂ) - ψ p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_natCast_cpow_of_pos hp.pos, neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (Nat.one_lt_cast.2 hp.one_lt) (neg_lt_zero.2 hs)
  have hn : ‖ψ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (ψ.norm_le_one _)) hpow
  rw [(sub_eq_zero.1 h).symm, norm_one] at hn
  exact lt_irrefl _ hn

/-- Euler-factor stripping: `ZeroFreeAll` (primitive characters) implies
`DirichletLNonvanishingRightOfHalf` (all Dirichlet characters, primitive and imprimitive). -/
theorem imprimitive_of_zeroFreeAll (hZ : ZeroFreeAll) : DirichletLNonvanishingRightOfHalf := by
  intro N _ χ s hre hs hz
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h0 : 0 < s.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hre
  have hcond : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
    rcases hs with hχ | hs1
    · left
      intro h1; apply hχ
      rw [← χ.changeLevel_primitiveCharacter, h1, map_one]
    · exact Or.inr hs1
  have hk := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter hcond
  rw [χ.changeLevel_primitiveCharacter, hz] at hk
  have hL : LFunction χ.primitiveCharacter s = 0 :=
    (mul_eq_zero.mp hk.symm).resolve_right
      (Finset.prod_ne_zero_iff.mpr fun p hp =>
        euler_factor_ne_zero _ h0 p (Nat.prime_of_mem_primeFactors hp))
  exact hZ (PChar.of χ) s hre hL

/-- Functional-equation reflection `s ↦ 1 - s`: `DirichletLNonvanishingRightOfHalf` implies
`DirichletLZerosOnLine` (all critical-strip zeros lie on `Re(s) = 1/2`). -/
theorem strip_of_right (hRight : DirichletLNonvanishingRightOfHalf) : DirichletLZerosOnLine := by
  intro N _ χ s h0 h1 hz
  have hs0 : s ≠ 0 := fun e => by rw [e, zero_re] at h0; exact lt_irrefl _ h0
  have hs1 : s ≠ 1 := fun e => by rw [e, one_re] at h1; exact lt_irrefl _ h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    let ψ := χ.primitiveCharacter
    have hL : LFunction ψ s = 0 := by
      have hk := LFunction_changeLevel χ.conductor_dvd_level ψ (Or.inr hs1)
      rw [χ.changeLevel_primitiveCharacter, hz] at hk
      exact (mul_eq_zero.mp hk.symm).resolve_right
        (Finset.prod_ne_zero_iff.mpr fun p hp =>
          euler_factor_ne_zero _ h0 p (Nat.prime_of_mem_primeFactors hp))
    have hG : gammaFactor ψ s ≠ 0 := by
      rcases ψ.even_or_odd with he | ho
      · rw [he.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos h0
      · rw [ho.gammaFactor_def]
        exact Gammaℝ_ne_zero_of_re_pos (by rw [add_re, one_re]; linarith)
    have hc : completedLFunction ψ s = 0 := by
      rw [LFunction_eq_completed_div_gammaFactor ψ s (Or.inl hs0), div_eq_zero_iff] at hL
      exact hL.resolve_right hG
    have hψ : ψ⁻¹.IsPrimitive := by
      rw [isPrimitive_def, conductor_inv]; exact χ.primitiveCharacter_isPrimitive
    have hfe := hψ.completedLFunction_one_sub s
    rw [inv_inv, hc, mul_zero] at hfe
    refine hRight χ.conductor ψ⁻¹ (1 - s) (by rw [sub_re, one_re]; linarith)
      (Or.inr fun e => hs0 (sub_eq_self.1 e)) ?_
    rw [LFunction_eq_completed_div_gammaFactor ψ⁻¹ (1 - s) (Or.inl (sub_ne_zero.2 hs1.symm)),
      hfe, zero_div]
  · exact hRight N χ s hgt (Or.inr hs1) hz

/-- Specialization `ζ(s) = L(1, s)` + functional equation of `completedRiemannZeta`:
`DirichletLZerosOnLine` implies `RiemannHypothesis`. -/
theorem riemannHypothesis_of_strip (hLine : DirichletLZerosOnLine) : RiemannHypothesis := by
  intro s hz htriv hs1
  have hs0 : s ≠ 0 := fun e => by rw [e, riemannZeta_zero] at hz; norm_num at hz
  rcases lt_or_ge 0 s.re with hpos | hnpos
  · rcases lt_or_ge s.re 1 with hlt1 | hge1
    · exact hLine 1 1 s hpos hlt1 (by rwa [LFunction_modOne_eq])
    · exact absurd hz (riemannZeta_ne_zero_of_one_le_re hge1)
  · exfalso
    have hG : Gammaℝ s ≠ 0 := fun hg => by
      obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hg
      rcases n with _ | n
      · exact hs0 (by simpa using hn)
      · exact htriv ⟨n, by rw [hn]; push_cast; ring⟩
    have hc : completedRiemannZeta s = 0 := by
      rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hz
      exact hz.resolve_right hG
    have h1s : 1 - s ≠ 0 := fun e => by
      have hr := congrArg Complex.re e
      rw [sub_re, one_re, zero_re] at hr; linarith
    have hz' : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_def_of_ne_zero h1s, completedRiemannZeta_one_sub, hc, zero_div]
    exact riemannZeta_ne_zero_of_one_le_re (by rw [sub_re, one_re]; linarith) hz'

/-- All 5 headline RH/GRH theorems deduced directly from `AllLevelsWindowBound la` (`1 < la`). -/
theorem LFunction_ne_zero_of_half_lt_re_of_windows {la : ℝ} (hla : 1 < la)
    (hW : AllLevelsWindowBound la) : DirichletLNonvanishingRightOfHalf :=
  imprimitive_of_zeroFreeAll (zeroFreeAll_of_allLevelsWindowBound hla hW)

theorem LFunction_eq_zero_re_of_windows {la : ℝ} (hla : 1 < la)
    (hW : AllLevelsWindowBound la) : DirichletLZerosOnLine :=
  strip_of_right (LFunction_ne_zero_of_half_lt_re_of_windows hla hW)

theorem LFunction_eq_zero_re_of_isPrimitive_of_windows {la : ℝ} (hla : 1 < la)
    (hW : AllLevelsWindowBound la) : PrimitiveDirichletLZerosOnLine :=
  fun N _ χ _ s => LFunction_eq_zero_re_of_windows hla hW N χ s

theorem riemannHypothesis_of_windows {la : ℝ} (hla : 1 < la)
    (hW : AllLevelsWindowBound la) : RiemannHypothesis :=
  riemannHypothesis_of_strip (LFunction_eq_zero_re_of_windows hla hW)

theorem riemannZeta_eq_zero_re_of_windows {la : ℝ} (hla : 1 < la)
    (hW : AllLevelsWindowBound la) : RiemannZetaZerosOnLine :=
  riemannHypothesis_of_windows hla hW

end RHDirect
