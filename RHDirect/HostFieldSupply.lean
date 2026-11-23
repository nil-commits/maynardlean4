import RHDirect.Interfaces
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.PrimesCongruentOne

/-!
# RHDirect.HostFieldSupply

Compact, direct, zero-`sorry`, zero-`axiom` Lean 4 rebuild of the **Cyclotomic / CM Host-Field
Supply, Short Norms & Coprime Rank Construction** against `RHDirect.Interfaces` and Mathlib
`v4.33.1`.

This module consolidates the live arithmetic/combinatorial core of:
- `Development/AutomorphicArithmetic/CharacterBoxes/` (`PairHyp.lean`, `IsChiField.lean`,
  `KerChiAny.lean`, `OrdAny.lean`, `FieldChi.lean`, `WinPairs.lean`, `RealSplit.lean`,
  `SupplyChi.lean`)
- `Development/AutomorphicArithmetic/CoprimeRanks/` (`AnyFramewindow.lean`, `FieldAny.lean`,
  `SecondSetNoRelation.lean`, `AdmChi.lean`)
- `Development/AutomorphicArithmetic/ShortNorms/` (`ShortNorm.lean`,
  `ExistsThreePrimesOneModLeRpow.lean`, `MulLogLeRpowEventually.lean`, `levelData.lean`)

## Structure
1. **Auxiliary Prime-Pair Reciprocity (`HostHyp`, `WinPair`)**: Quadratic reciprocity for
   `q ≡ 3 (mod 8)`, `d ≡ 7 (mod 16)`, `q ∣ d + 1`, and small odd-prime splitting.
2. **Cyclotomic 2-Tower & Minimal Conductor (`HGrp`, `CharQuot`, `QS`)**:
   - Exact order `Nat.card (HGrp e) = 2 ^ e` of `(ZMod (2^(e+2)))ˣ ⧸ ⟨-1⟩`
   - Minimal conductor `QS Ξ e ∣ lcm (2^(e+2)) M` with `2^(e+2) ∣ QS Ξ e`
   - Chinese Remainder Theorem divisibility `M ∣ QS (zpowers χ) e` for primitive `χ`
   - Exactness of `QS Ξ e` at every prime divisor `l ∣ QS Ξ e`
   - Antitone kernel stabilization `∃ c e₀, ∀ e ≥ e₀, towerOrd Ξ e = c * 2 ^ e` and
     dyadic window covering `∃ e ≥ e₀, W ≤ towerOrd Ξ e ≤ 2 * W`
3. **CM Host-Field Bridge (`HostCyclotomicDatum`, `KerChi`, `isChiField_of_kerChi`)**:
   Direct Artin-kernel equivalence connecting cyclotomic host fields to `RHDirect.IsChiField`,
   plus exact product-homomorphism kernel characterization and host-character parity/real-twist
   tracking.
4. **`WinPair` / `PageN` Window Covering & `401 = 400 + 1` Scaling (`winPairs_supply`)**:
   Direct rescaling of `VWinAt S ψ 401` on `[W, W²]` to `[Z, Z^(3/2)]` with `PageN` coverage and
   `⌊x ^ 400⌋₊` cutoff monotonicity.
5. **Short Norms, Coprime Level Primes & Large-Scale Rank Dominance**:
   - `exists_three_primes_one_mod_le_rpow` (`SmallOne →` three distinct primes `≡ 1 mod 15N, N`
     bounded by `N ^ C8`)
   - Unconditional `exists_four_coprime_level_primes` (Dirichlet / `Nat.exists_prime_gt_modEq_one`)
   - `mul_log_le_rpow_eventually`, `mod_log_small_eventually`, and `qd_gt_rank_product_eventually`
     (`4 * t * r + 1 < q, d` and `100 ≤ d`)
   - `span_natCast_ne_top_of_one_lt` in `𝓞 K`
6. **Cyclic Level Bounds & Unified Host-Field Supply Assembly**:
   Totient/real-order bounds on `Level.cyc ψ`, evenness characterization, and the combined
   `hostFieldSupply_assembly` theorem feeding `AnalyticBridge.lean` and `GaloisModularityCore.lean`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open NumberField Filter

namespace RHDirect

namespace HostFieldSupply

/-! ## 1. Auxiliary Prime-Pair Arithmetic & Quadratic Reciprocity (`PairHyp`) -/

/-- Core arithmetic hypotheses on an auxiliary prime pair `(q, d)` (`HostHyp`). -/
structure HostHyp (q d : ℕ) : Prop where
  q_prime : q.Prime
  d_prime : d.Prime
  q_mod : q % 8 = 3
  d_mod : d % 16 = 7
  jac_neg_d_q : jacobiSym (-(d : ℤ)) q = 1

theorem jacobiSym_neg_of_dvd_succ {p d : ℕ} (h : p ∣ d + 1) :
    jacobiSym (-(d : ℤ)) p = 1 := by
  have h1 : (-(d : ℤ)) ≡ 1 [ZMOD (p : ℤ)] := by
    apply Int.modEq_iff_dvd.2
    have h2 := Int.natCast_dvd_natCast.2 h
    push_cast at h2
    have h3 : (1 : ℤ) - -(d : ℤ) = (d : ℤ) + 1 := by ring
    rw [h3]
    exact h2
  rw [jacobiSym.mod_left' h1, jacobiSym.one_left]

theorem jacobiSym_neg_eq_reciprocity {n a : ℕ} (hn : n % 4 = 3) (ha : Odd a) :
    jacobiSym (-(n : ℤ)) a = jacobiSym (a : ℤ) n := by
  have hno : Odd n := Nat.odd_iff.2 (by omega)
  rw [jacobiSym.neg _ ha]
  rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 ha) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h hno]
  · rw [ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four h hn]
    ring

theorem jacobiSym_congr_nat {a b m : ℕ} (h : a ≡ b [MOD m]) :
    jacobiSym (a : ℤ) m = jacobiSym (b : ℤ) m :=
  jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr h)

theorem HostHyp.q_ne_two {q d : ℕ} (h : HostHyp q d) : q ≠ 2 := by
  have := h.q_mod
  omega

theorem HostHyp.d_ne_two {q d : ℕ} (h : HostHyp q d) : d ≠ 2 := by
  have := h.d_mod
  omega

theorem HostHyp.q_ne_d {q d : ℕ} (h : HostHyp q d) : q ≠ d := by
  have h1 := h.q_mod
  have h2 := h.d_mod
  omega

theorem HostHyp.coprime_q_d {q d : ℕ} (h : HostHyp q d) : Nat.Coprime q d :=
  (Nat.coprime_primes h.q_prime h.d_prime).mpr h.q_ne_d

theorem HostHyp.odd_q {q d : ℕ} (h : HostHyp q d) : Odd q :=
  Nat.odd_iff.2 (by have := h.q_mod; omega)

theorem HostHyp.odd_d {q d : ℕ} (h : HostHyp q d) : Odd d :=
  Nat.odd_iff.2 (by have := h.d_mod; omega)

/-- Extract `HostHyp`, small-prime splitting, and quadratic reciprocity from `WinPair`. -/
theorem winPair_reciprocity {eps Y : ℝ} {q d : ℕ} (hw : WinPair eps Y q d) :
    HostHyp q d ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ Y ^ (eps / 5) → jacobiSym (-(d : ℤ)) p = 1) ∧
      (∀ a : ℕ, Odd a →
        jacobiSym (-(q : ℤ)) a = jacobiSym (a : ℤ) q ∧
        jacobiSym (-(d : ℤ)) a = jacobiSym (a : ℤ) d) := by
  have hq4 : q % 4 = 3 := by have := hw.q_mod; omega
  have hd4 : d % 4 = 3 := by have := hw.d_mod; omega
  refine ⟨⟨hw.q_prime, hw.d_prime, hw.q_mod, hw.d_mod, jacobiSym_neg_of_dvd_succ hw.d_q⟩, ?_, ?_⟩
  · intro p hp hp2 hpY
    exact jacobiSym_neg_of_dvd_succ (hw.d_small p hp hp2 hpY)
  · intro a ha
    exact ⟨jacobiSym_neg_eq_reciprocity hq4 ha, jacobiSym_neg_eq_reciprocity hd4 ha⟩

theorem winPair_q_le_exp {eps Y : ℝ} {q d : ℕ} (hw : WinPair eps Y q d) :
    (q : ℝ) ≤ Real.exp (Y ^ (eps / 5)) :=
  (Real.log_le_iff_le_exp (by exact_mod_cast hw.q_prime.pos)).1 hw.q_up

theorem winPair_d_le_exp {eps Y : ℝ} {q d : ℕ} (hw : WinPair eps Y q d) :
    (d : ℝ) ≤ Real.exp (Y ^ (eps / 5) * Real.log Y ^ 2) :=
  (Real.log_le_iff_le_exp (by exact_mod_cast hw.d_prime.pos)).1 hw.d_up

theorem winPair_q_ne_three {eps Y : ℝ} {q d : ℕ} (hw : WinPair eps Y q d)
    (hY : 6 ≤ Y ^ (eps / 5)) : q ≠ 3 := by
  rintro rfl
  have h1 : Real.log (3 : ℝ) ≤ 2 := by
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have h2 := hw.q_lo
  push_cast at h2
  linarith

/-! ## 2. Cyclotomic 2-Tower, Minimal Conductor `QS`, CRT Divisibility & Window Covering -/

/-- Conductor divisor and size bounds when `Q ∣ lcm (2^(e+2)) M`. -/
theorem conductor_divisor_bounds {M : ℕ} [NeZero M] {Q e b : ℕ}
    (hQ : Q ∣ Nat.lcm (2 ^ (e + 2)) M) (hb : 4 * M ≤ b) :
    (∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ Q → l ∣ M ∧ 4 * l ≤ b) ∧ Q ≤ 4 * M * 2 ^ e := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h1 : Q ∣ 2 ^ (e + 2) * M := hQ.trans (Nat.lcm_dvd_mul _ _)
  refine ⟨fun l hl h2 h => ?_, ?_⟩
  · have h3 : l ∣ M := (hl.dvd_mul.1 (h.trans h1)).resolve_left fun h4 =>
      h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h4))
    have hle : l ≤ M := Nat.le_of_dvd hM h3
    exact ⟨h3, by omega⟩
  · have hle := Nat.le_of_dvd (Nat.mul_pos (by positivity) hM) h1
    calc Q ≤ 2 ^ (e + 2) * M := hle
      _ = 4 * M * 2 ^ e := by ring

/-- Helper: composition of `ZMod.unitsMap` along a divisibility chain. -/
theorem unitsMap_unitsMap {a b c : ℕ} (h1 : a ∣ b) (h2 : b ∣ c) (u : (ZMod c)ˣ) :
    ZMod.unitsMap h1 (ZMod.unitsMap h2 u) = ZMod.unitsMap (h1.trans h2) u := by
  rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp]

/-- Helper: `ZMod.unitsMap` preserves `-1`. -/
theorem unitsMap_neg_one {a b : ℕ} (h : a ∣ b) :
    ZMod.unitsMap h (-1 : (ZMod b)ˣ) = (-1 : (ZMod a)ˣ) := by
  apply Units.ext
  change (ZMod.castHom h (ZMod a)) (-1 : ZMod b) = (-1 : ZMod a)
  rw [map_neg, map_one]

/-- Helper: `ZMod.unitsMap` maps `ZMod.unitOfCoprime a h` to `ZMod.unitOfCoprime a (h.coprime_dvd_right hd)`. -/
theorem unitsMap_unitOfCoprime {a m n : ℕ} (hd : m ∣ n) (h : a.Coprime n) :
    ZMod.unitsMap hd (ZMod.unitOfCoprime a h) =
      ZMod.unitOfCoprime a (h.coprime_dvd_right hd) := by
  apply Units.ext
  change ZMod.castHom hd (ZMod m) (a : ZMod n) = (a : ZMod m)
  rw [map_natCast]

/-- Helper: `ZMod.unitsMap` preserves `.val` modulo the target modulus. -/
theorem unitsMap_val_modEq {m n : ℕ} [NeZero m] [NeZero n] (hd : m ∣ n) (u : (ZMod n)ˣ) :
    ((ZMod.unitsMap hd u : ZMod m).val) ≡ (u : ZMod n).val [MOD m] := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  change ZMod.castHom hd (ZMod m) (u : ZMod n) = ((u : ZMod n).val : ZMod m)
  conv_lhs => rw [← ZMod.natCast_zmod_val (u : ZMod n)]
  rw [map_natCast]

/-- Helper: `ZMod.unitsMap hd u = 1` iff `(u : ZMod n).val ≡ 1 [MOD m]`. -/
theorem unitsMap_eq_one_iff {m n : ℕ} [NeZero m] [NeZero n] (hd : m ∣ n) (u : (ZMod n)ˣ) :
    ZMod.unitsMap hd u = 1 ↔ (u : ZMod n).val ≡ 1 [MOD m] := by
  rw [Units.ext_iff, Units.val_one]
  change ZMod.castHom hd (ZMod m) (u : ZMod n) = 1 ↔ _
  conv_lhs => rw [← ZMod.natCast_zmod_val (u : ZMod n), map_natCast, ← Nat.cast_one (R := ZMod m)]
  exact ZMod.natCast_eq_natCast_iff _ _ _

/-- The real 2-power cyclotomic Galois quotient `HGrp e := (ZMod (2^(e+2)))ˣ ⧸ ⟨-1⟩` of order `2^e`. -/
abbrev HGrp (e : ℕ) : Type :=
  (ZMod (2 ^ (e + 2)))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ)

/-- Canonical quotient homomorphism `(ZMod (2^(e+2)))ˣ →* HGrp e`. -/
def hcl (e : ℕ) : (ZMod (2 ^ (e + 2)))ˣ →* HGrp e :=
  QuotientGroup.mk' (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))

theorem hcl_surjective (e : ℕ) : Function.Surjective (hcl e) :=
  QuotientGroup.mk'_surjective _

theorem hcl_eq_one_iff (e : ℕ) (u : (ZMod (2 ^ (e + 2)))ˣ) :
    hcl e u = 1 ↔ u = 1 ∨ u = -1 := by
  rw [hcl, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]
    rcases Int.even_or_odd k with hk2 | hk2
    · exact Or.inl hk2.neg_one_zpow
    · exact Or.inr hk2.neg_one_zpow
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem hcl_nat_eq_one_iff (e a : ℕ) (h : a.Coprime (2 ^ (e + 2))) :
    hcl e (ZMod.unitOfCoprime a h) = 1 ↔
      (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) := by
  rw [hcl_eq_one_iff, Units.ext_iff, Units.ext_iff, ZMod.coe_unitOfCoprime, Units.val_neg,
    Units.val_one]
  apply or_congr
  · rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
  · rw [eq_neg_iff_add_eq_zero, ← Nat.cast_one, ← Nat.cast_add, ZMod.natCast_eq_zero_iff,
      Nat.modEq_zero_iff_dvd]

/-- The order of `HGrp e` is exact: `Nat.card (HGrp e) = 2 ^ e`. -/
theorem card_HGrp (e : ℕ) : Nat.card (HGrp e) = 2 ^ e := by
  have : NeZero (2 ^ (e + 2)) := ⟨by positivity⟩
  set K : Subgroup (ZMod (2 ^ (e + 2)))ˣ := Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ)
  have hneg_ne : (-1 : (ZMod (2 ^ (e + 2)))ˣ) ≠ 1 := by
    intro h
    have hv := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one, neg_eq_iff_add_eq_zero, one_add_one_eq_two] at hv
    have hd : 2 ^ (e + 2) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 ^ (e + 2))).1 (by simpa using hv)
    have h4 : 4 ≤ 2 ^ (e + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hle := Nat.le_of_dvd (by norm_num) hd
    omega
  have hord : orderOf (-1 : (ZMod (2 ^ (e + 2)))ˣ) = 2 :=
    orderOf_eq_prime (by simp) hneg_ne
  have hcardK : Nat.card K = 2 := by
    rw [Nat.card_zpowers, hord]
  have htot : Nat.card (ZMod (2 ^ (e + 2)))ˣ = 2 ^ (e + 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp
  have hlag := Subgroup.card_mul_index K
  have hq : Nat.card (HGrp e) = K.index := rfl
  rw [hcardK, htot] at hlag
  rw [hq]
  have h2 : 2 * 2 ^ e = 2 ^ (e + 1) := by ring
  omega

/-- Helper: value of `χ⁻¹` at a unit `u : (ZMod M)ˣ` equals `(χ u)⁻¹`. -/
theorem mulChar_inv_apply_unit {M : ℕ} (χ : DirichletCharacter ℂ M) (u : (ZMod M)ˣ) :
    χ⁻¹ (u : ZMod M) = (χ (u : ZMod M))⁻¹ := by
  have h1 : χ⁻¹ (u : ZMod M) * χ (u : ZMod M) = 1 := by
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply_coe]
  exact eq_inv_of_mul_eq_one_left h1

/-- Annihilator subgroup of a subgroup `Ξ` of Dirichlet characters mod `M`. -/
def charAnn {M : ℕ} (Ξ : Subgroup (DirichletCharacter ℂ M)) : Subgroup (ZMod M)ˣ where
  carrier := {u | ∀ χ ∈ Ξ, χ u = 1}
  mul_mem' ha hb χ hχ := by rw [Units.val_mul, map_mul, ha χ hχ, hb χ hχ, mul_one]
  one_mem' χ _ := by rw [Units.val_one, map_one]
  inv_mem' := by
    intro u ha χ hχ
    have h1 : χ (u⁻¹ : (ZMod M)ˣ) * χ u = 1 := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    rw [ha χ hχ, mul_one] at h1
    exact h1

theorem mem_charAnn_iff {M : ℕ} (Ξ : Subgroup (DirichletCharacter ℂ M)) (u : (ZMod M)ˣ) :
    u ∈ charAnn Ξ ↔ ∀ χ ∈ Ξ, χ u = 1 := Iff.rfl

theorem mem_charAnn_zpowers {M : ℕ} (χ : DirichletCharacter ℂ M) (u : (ZMod M)ˣ) :
    u ∈ charAnn (Subgroup.zpowers χ) ↔ χ u = 1 := by
  rw [mem_charAnn_iff]
  constructor
  · intro h
    exact h χ (Subgroup.mem_zpowers χ)
  · intro h ψ hψ
    rw [Subgroup.zpowers_eq_closure] at hψ
    induction hψ using Subgroup.closure_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact h
    | one => exact MulChar.one_apply_coe u
    | mul x y _ _ hx hy => rw [MulChar.mul_apply, hx, hy, one_mul]
    | inv x _ hx => rw [mulChar_inv_apply_unit, hx, inv_one]

/-- The finite character quotient `CharQuot Ξ := (ZMod M)ˣ ⧸ charAnn Ξ`. -/
abbrev CharQuot {M : ℕ} (Ξ : Subgroup (DirichletCharacter ℂ M)) : Type :=
  (ZMod M)ˣ ⧸ charAnn Ξ

/-- Canonical surjection `(ZMod M)ˣ →* CharQuot Ξ`. -/
def charQuotMk {M : ℕ} (Ξ : Subgroup (DirichletCharacter ℂ M)) : (ZMod M)ˣ →* CharQuot Ξ :=
  QuotientGroup.mk' (charAnn Ξ)

theorem charQuotMk_surjective {M : ℕ} (Ξ : Subgroup (DirichletCharacter ℂ M)) :
    Function.Surjective (charQuotMk Ξ) :=
  QuotientGroup.mk'_surjective _

theorem charQuotMk_eq_one_iff {M : ℕ} (Ξ : Subgroup (DirichletCharacter ℂ M)) (u : (ZMod M)ˣ) :
    charQuotMk Ξ u = 1 ↔ ∀ χ ∈ Ξ, χ u = 1 := by
  rw [charQuotMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_charAnn_iff]

theorem charQuotMk_zpowers_eq_one_iff {M : ℕ} (χ : DirichletCharacter ℂ M) (u : (ZMod M)ˣ) :
    charQuotMk (Subgroup.zpowers χ) u = 1 ↔ χ u = 1 := by
  rw [charQuotMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_charAnn_zpowers]

/-- Combined quotient map `xiL Ξ e : (ZMod (lcm (2^(e+2)) M))ˣ →* CharQuot Ξ`. -/
def xiL {M : ℕ} (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ →* CharQuot Ξ :=
  (charQuotMk Ξ).comp (ZMod.unitsMap (Nat.dvd_lcm_right (2 ^ (e + 2)) M))

/-- Combined 2-tower quotient map `hclL M e : (ZMod (lcm (2^(e+2)) M))ˣ →* HGrp e`. -/
def hclL (M e : ℕ) : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ →* HGrp e :=
  (hcl e).comp (ZMod.unitsMap (Nat.dvd_lcm_left (2 ^ (e + 2)) M))

/-- Joint Galois image map `etaMap Ξ e : (ZMod (lcm (2^(e+2)) M))ˣ →* HGrp e × CharQuot Ξ`. -/
def etaMap {M : ℕ} (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ →* HGrp e × CharQuot Ξ :=
  MonoidHom.prod (hclL M e) (xiL Ξ e)

/-- Admissible conductor `Q` for `(Ξ, e)`: divides `lcm (2^(e+2)) M`, divisible by `2^(e+2)`,
and `xiL Ξ e` factors modulo `Q`. -/
def GoodMod {M : ℕ} (Ξ : Subgroup (DirichletCharacter ℂ M)) (e Q : ℕ) : Prop :=
  Q ∣ Nat.lcm (2 ^ (e + 2)) M ∧
  2 ^ (e + 2) ∣ Q ∧
  ∀ u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ,
    (u : ZMod (Nat.lcm (2 ^ (e + 2)) M)).val ≡ 1 [MOD Q] → xiL Ξ e u = 1

theorem goodMod_lcm {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    GoodMod Ξ e (Nat.lcm (2 ^ (e + 2)) M) := by
  have : NeZero (Nat.lcm (2 ^ (e + 2)) M) := ⟨Nat.lcm_ne_zero (by positivity) (NeZero.ne M)⟩
  refine ⟨dvd_refl _, Nat.dvd_lcm_left _ _, fun u hu => ?_⟩
  have hu1 : u = 1 := by
    apply Units.ext
    rw [Units.val_one, ← ZMod.natCast_zmod_val (u : ZMod (Nat.lcm (2 ^ (e + 2)) M)), ← Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu
  rw [hu1, map_one]

open Classical in
/-- Minimal conductor `QS Ξ e` of the cyclotomic character-box base field. -/
def QS {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) : ℕ :=
  Nat.find ⟨Nat.lcm (2 ^ (e + 2)) M, goodMod_lcm Ξ e⟩

theorem goodMod_QS {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    GoodMod Ξ e (QS Ξ e) := by
  classical
  exact Nat.find_spec ⟨Nat.lcm (2 ^ (e + 2)) M, goodMod_lcm Ξ e⟩

theorem QS_min {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e Q : ℕ)
    (hQ : GoodMod Ξ e Q) : QS Ξ e ≤ Q := by
  classical
  exact Nat.find_min' ⟨Nat.lcm (2 ^ (e + 2)) M, goodMod_lcm Ξ e⟩ hQ

theorem QS_dvd_lcm {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    QS Ξ e ∣ Nat.lcm (2 ^ (e + 2)) M := (goodMod_QS Ξ e).1

theorem two_pow_dvd_QS {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    2 ^ (e + 2) ∣ QS Ξ e := (goodMod_QS Ξ e).2.1

theorem QS_pos {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    0 < QS Ξ e :=
  Nat.pos_of_ne_zero fun h => by
    have hd := two_pow_dvd_QS Ξ e
    rw [h] at hd
    have hL := QS_dvd_lcm Ξ e
    rw [h] at hL
    exact Nat.lcm_ne_zero (by positivity) (NeZero.ne M) (zero_dvd_iff.mp hL)

theorem QS_dvd_mul {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    QS Ξ e ∣ 2 ^ (e + 2) * M :=
  (QS_dvd_lcm Ξ e).trans (Nat.lcm_dvd_mul _ _)

theorem QS_le_mul {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    QS Ξ e ≤ 4 * M * 2 ^ e :=
  (conductor_divisor_bounds (QS_dvd_lcm Ξ e) le_rfl).2

theorem QS_coprime_of_coprime {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M))
    {e q d : ℕ} (hH : HostHyp q d) (hc : Nat.Coprime M (q * d)) :
    Nat.Coprime (QS Ξ e) (q * d) := by
  have h2q : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hH.q_prime).mpr hH.q_ne_two.symm
  have h2d : Nat.Coprime 2 d := (Nat.coprime_primes Nat.prime_two hH.d_prime).mpr hH.d_ne_two.symm
  have h2qd : Nat.Coprime (2 ^ (e + 2)) (q * d) := (h2q.mul_right h2d).pow_left _
  exact (h2qd.mul_left hc).coprime_dvd_left (QS_dvd_mul Ξ e)

theorem QS_coprime_fifteen {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)
    (h : Nat.Coprime M 15) : Nat.Coprime (QS Ξ e) 15 :=
  (Nat.Coprime.mul_left (Nat.Coprime.pow_left _ (by norm_num)) h).coprime_dvd_left (QS_dvd_mul Ξ e)

/-- **CRT Conductor Divisibility (`dvd_QS`)**: For any primitive Dirichlet character `χ` mod `M`,
the conductor `M` divides the minimal cyclotomic host conductor `QS (zpowers χ) e`. -/
theorem primitive_conductor_dvd_QS {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    (hχ : χ.IsPrimitive) (e : ℕ) : M ∣ QS (Subgroup.zpowers χ) e := by
  obtain ⟨hQL, h2Q, hgood⟩ := goodMod_QS (Subgroup.zpowers χ) e
  set Q := QS (Subgroup.zpowers χ) e
  have : NeZero (Nat.lcm (2 ^ (e + 2)) M) := ⟨Nat.lcm_ne_zero (by positivity) (NeZero.ne M)⟩
  have hQpos : 0 < Q := QS_pos (Subgroup.zpowers χ) e
  have : NeZero (Q.gcd M) := ⟨(Nat.gcd_pos_of_pos_left M hQpos).ne'⟩
  have hf : χ.FactorsThrough (Q.gcd M) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.gcd_dvd_right Q M)).mpr ?_
    intro x hx
    rw [MonoidHom.mem_ker, unitsMap_eq_one_iff] at hx
    obtain ⟨z, hz1, hz2⟩ := Nat.chineseRemainder' hx.symm
    have hzM : z.Coprime M := hz2.gcd_eq.trans (ZMod.val_coe_unit_coprime x)
    have hzQ : z.Coprime Q := hz1.gcd_eq.trans (Nat.gcd_one_left Q)
    have hz2e : z.Coprime (2 ^ (e + 2)) := hzQ.coprime_dvd_right h2Q
    have hzL : z.Coprime (Nat.lcm (2 ^ (e + 2)) M) :=
      (Nat.Coprime.mul_right hz2e hzM).coprime_dvd_right (Nat.lcm_dvd_mul _ _)
    have hw := hgood (ZMod.unitOfCoprime z hzL) (by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      exact ((Nat.mod_modEq z _).of_dvd hQL).trans hz1)
    rw [xiL, MonoidHom.comp_apply, charQuotMk_zpowers_eq_one_iff, unitsMap_unitOfCoprime] at hw
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
    have hx' : ((ZMod.unitOfCoprime z (hzL.coprime_dvd_right (Nat.dvd_lcm_right _ _)) :
        (ZMod M)ˣ) : ZMod M) = x := by
      rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val (x : ZMod M)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hz2
    rw [← hx']
    exact hw
  have hc0 : χ.conductor ≤ Q.gcd M := Nat.sInf_le hf
  have hχ' : χ.conductor = M := hχ
  rw [hχ'] at hc0
  have hg : Q.gcd M = M :=
    le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (Nat.gcd_dvd_right _ _)) hc0
  have h := Nat.gcd_dvd_left Q M
  rwa [hg] at h

/-- **Exactness of `QS Ξ e`**: For `1 ≤ e` and every prime `l ∣ QS Ξ e`, there exists a unit
`u : (ZMod (lcm (2^(e+2)) M))ˣ` with `u ≡ 1 (mod QS Ξ e / l)` acting nontrivially on
`HGrp e × CharQuot Ξ`. -/
theorem QS_exact_witness {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) {e : ℕ}
    (he : 1 ≤ e) {l : ℕ} (hl : l.Prime) (hd : l ∣ QS Ξ e) :
    ∃ u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ,
      (u : ZMod (Nat.lcm (2 ^ (e + 2)) M)).val ≡ 1 [MOD QS Ξ e / l] ∧ etaMap Ξ e u ≠ 1 := by
  have : NeZero (Nat.lcm (2 ^ (e + 2)) M) := ⟨Nat.lcm_ne_zero (by positivity) (NeZero.ne M)⟩
  have hQpos : 0 < QS Ξ e := QS_pos Ξ e
  have hlt : QS Ξ e / l < QS Ξ e := Nat.div_lt_self hQpos hl.one_lt
  have hdv : QS Ξ e / l ∣ QS Ξ e := Nat.div_dvd_of_dvd hd
  by_cases h2 : 2 ^ (e + 2) ∣ QS Ξ e / l
  · by_contra hn
    push Not at hn
    have hnot : ¬ GoodMod Ξ e (QS Ξ e / l) := by
      classical
      exact Nat.find_min ⟨Nat.lcm (2 ^ (e + 2)) M, goodMod_lcm Ξ e⟩ hlt
    apply hnot
    refine ⟨hdv.trans (QS_dvd_lcm Ξ e), h2, fun u hu => ?_⟩
    exact congrArg Prod.snd (hn u hu)
  · obtain ⟨c, hc⟩ := two_pow_dvd_QS Ξ e
    have hl2 : l = 2 := by
      by_contra h3
      have h4 : Nat.Coprime (2 ^ (e + 2)) l :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm h3))
      exact h2 (h4.dvd_of_dvd_mul_right (by rw [Nat.div_mul_cancel hd]; exact two_pow_dvd_QS Ξ e))
    subst hl2
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    have hdiv : QS Ξ (k + 1) / 2 = 2 ^ (k + 2) * c := by
      rw [hc, show 2 ^ (k + 1 + 2) * c = 2 * (2 ^ (k + 2) * c) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
    have hQ : QS Ξ (k + 1) = 2 * (2 ^ (k + 2) * c) := by rw [hc]; ring
    have hcop : Nat.Coprime (2 ^ (k + 2) * c + 1) (QS Ξ (k + 1)) := by
      rw [hQ]
      refine Nat.Coprime.mul_right ?_ (by simp)
      rw [Nat.coprime_two_right]
      exact ⟨2 ^ (k + 1) * c, by ring⟩
    have : NeZero (QS Ξ (k + 1)) := ⟨hQpos.ne'⟩
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (QS_dvd_lcm Ξ (k + 1))
      (ZMod.unitOfCoprime (2 ^ (k + 2) * c + 1) hcop)
    have hval : (u : ZMod (Nat.lcm (2 ^ (k + 1 + 2)) M)).val ≡ 2 ^ (k + 2) * c + 1
        [MOD QS Ξ (k + 1)] := by
      have h1 := unitsMap_val_modEq (QS_dvd_lcm Ξ (k + 1)) u
      rw [hu, ZMod.coe_unitOfCoprime, ZMod.val_natCast] at h1
      exact h1.symm.trans (Nat.mod_modEq _ _)
    refine ⟨u, (hval.of_dvd hdv).trans (by rw [hdiv]; simp [Nat.ModEq]), fun h4 => ?_⟩
    have h5 : hcl (k + 1) (ZMod.unitsMap (Nat.dvd_lcm_left _ _) u) = 1 := congrArg Prod.fst h4
    have hmap : ZMod.unitsMap (Nat.dvd_lcm_left (2 ^ (k + 1 + 2)) M) u =
        ZMod.unitOfCoprime (2 ^ (k + 2) * c + 1)
          (hcop.coprime_dvd_right (two_pow_dvd_QS Ξ (k + 1))) := by
      rw [← unitsMap_unitOfCoprime (two_pow_dvd_QS Ξ (k + 1)) hcop, ← hu, unitsMap_unitsMap]
    rw [hmap, hcl_eq_one_iff, Units.ext_iff, Units.ext_iff, ZMod.coe_unitOfCoprime,
      Units.val_neg, Units.val_one, Nat.cast_add, Nat.cast_one] at h5
    rcases h5 with h5 | h5
    · refine h2 ?_
      rw [hdiv, ← ZMod.natCast_eq_zero_iff]
      linear_combination h5
    · have h6 : 2 ^ (k + 1 + 2) ∣ 2 ^ (k + 2) * c + 2 := by
        rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_ofNat]
        linear_combination h5
      have h7 : 4 ∣ 2 ^ (k + 2) * c + 2 := Dvd.dvd.trans ⟨2 ^ (k + 1), by ring⟩ h6
      have h8 : 4 ∣ 2 ^ (k + 2) * c := ⟨2 ^ k * c, by ring⟩
      omega

/-- The subgroup image of `etaMap Ξ e` inside `HGrp e × CharQuot Ξ`. -/
def etaRange {M : ℕ} (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    Subgroup (HGrp e × CharQuot Ξ) :=
  Subgroup.map (etaMap Ξ e) ⊤

/-- The cardinality `towerOrd Ξ e` of the joint Galois image `etaRange Ξ e` at tower level `e`. -/
def towerOrd {M : ℕ} (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) : ℕ :=
  Nat.card (etaRange Ξ e)

/-- Kernel slice `K(e) = (ker hclL).map xiL ≤ CharQuot Ξ` measuring the overlap between `Ξ` and
the 2-power cyclotomic tower. -/
def towerKernelSlice {M : ℕ} (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    Subgroup (CharQuot Ξ) :=
  (hclL M e).ker.map (xiL Ξ e)

/-- Exact degree factorization: `towerOrd Ξ e = Nat.card (towerKernelSlice Ξ e) * 2 ^ e`. -/
theorem towerOrd_eq_mul {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    towerOrd Ξ e = Nat.card (towerKernelSlice Ξ e) * 2 ^ e := by
  have : NeZero (Nat.lcm (2 ^ (e + 2)) M) := ⟨Nat.lcm_ne_zero (by positivity) (NeZero.ne M)⟩
  let p1 : etaRange Ξ e →* HGrp e :=
    (MonoidHom.fst (HGrp e) (CharQuot Ξ)).comp (etaRange Ξ e).subtype
  have hp1_surj : Function.Surjective p1 := by
    intro y
    obtain ⟨v, rfl⟩ := hcl_surjective e y
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (Nat.dvd_lcm_left (2 ^ (e + 2)) M) v
    refine ⟨⟨etaMap Ξ e u, ⟨u, Subgroup.mem_top _, rfl⟩⟩, ?_⟩
    change hcl e (ZMod.unitsMap (Nat.dvd_lcm_left (2 ^ (e + 2)) M) u) = hcl e v
    rw [hu]
  have hlag := Subgroup.card_mul_index p1.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hp1_surj, Subgroup.card_top, card_HGrp e] at hlag
  rw [towerOrd, ← hlag]
  congr 1
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨x.1.1.2, by
      obtain ⟨⟨⟨a, b⟩, u, _, hu⟩, hx⟩ := x
      refine ⟨u, ?_, congrArg Prod.snd hu⟩
      change hclL M e u = 1
      have h1 : a = 1 := hx
      exact (congrArg Prod.fst hu).trans h1⟩)
    ⟨?_, ?_⟩)
  · rintro ⟨⟨⟨a1, b1⟩, h1⟩, hx1⟩ ⟨⟨⟨a2, b2⟩, h2⟩, hx2⟩ h
    have ha1 : a1 = 1 := hx1
    have ha2 : a2 = 1 := hx2
    have hb : b1 = b2 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (Prod.ext (ha1.trans ha2.symm) hb))
  · rintro ⟨b, u, hu, rfl⟩
    exact ⟨⟨⟨etaMap Ξ e u, ⟨u, Subgroup.mem_top _, rfl⟩⟩, hu⟩, rfl⟩

/-- Antitonicity of the kernel slice along the 2-tower: `towerKernelSlice Ξ (e + 1) ≤ towerKernelSlice Ξ e`. -/
theorem towerKernelSlice_succ_le {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    towerKernelSlice Ξ (e + 1) ≤ towerKernelSlice Ξ e := by
  intro b hb
  obtain ⟨u, hu, rfl⟩ := hb
  have hp : 2 ^ (e + 2) ∣ 2 ^ (e + 1 + 2) := pow_dvd_pow 2 (by omega)
  have hL : Nat.lcm (2 ^ (e + 2)) M ∣ Nat.lcm (2 ^ (e + 1 + 2)) M :=
    Nat.lcm_dvd (hp.trans (Nat.dvd_lcm_left _ _)) (Nat.dvd_lcm_right _ _)
  refine ⟨ZMod.unitsMap hL u, ?_, ?_⟩
  · change hcl e (ZMod.unitsMap (Nat.dvd_lcm_left _ _) (ZMod.unitsMap hL u)) = 1
    have hu' : hcl (e + 1) (ZMod.unitsMap (Nat.dvd_lcm_left _ _) u) = 1 := hu
    rw [hcl_eq_one_iff] at hu' ⊢
    rw [unitsMap_unitsMap]
    have hcomp : ZMod.unitsMap ((Nat.dvd_lcm_left (2 ^ (e + 2)) M).trans hL) u =
        ZMod.unitsMap hp (ZMod.unitsMap (Nat.dvd_lcm_left (2 ^ (e + 1 + 2)) M) u) := by
      rw [unitsMap_unitsMap]
    rw [hcomp]
    rcases hu' with h | h
    · exact Or.inl (by rw [h, map_one])
    · exact Or.inr (by rw [h, unitsMap_neg_one])
  · change charQuotMk Ξ (ZMod.unitsMap (Nat.dvd_lcm_right _ _) (ZMod.unitsMap hL u)) =
      charQuotMk Ξ (ZMod.unitsMap (Nat.dvd_lcm_right _ _) u)
    rw [unitsMap_unitsMap]

theorem towerOrd_succ_le {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    towerOrd Ξ (e + 1) ≤ 2 * towerOrd Ξ e := by
  rw [towerOrd_eq_mul, towerOrd_eq_mul]
  have hle : Nat.card (towerKernelSlice Ξ (e + 1)) ≤ Nat.card (towerKernelSlice Ξ e) :=
    Subgroup.card_le_of_le (towerKernelSlice_succ_le Ξ e)
  calc Nat.card (towerKernelSlice Ξ (e + 1)) * 2 ^ (e + 1)
      ≤ Nat.card (towerKernelSlice Ξ e) * 2 ^ (e + 1) := Nat.mul_le_mul_right _ hle
    _ = 2 * (Nat.card (towerKernelSlice Ξ e) * 2 ^ e) := by ring

theorem two_pow_le_towerOrd {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    2 ^ e ≤ towerOrd Ξ e := by
  rw [towerOrd_eq_mul]
  have h1 : 1 ≤ Nat.card (towerKernelSlice Ξ e) := Nat.card_pos
  calc 2 ^ e = 1 * 2 ^ e := (one_mul _).symm
    _ ≤ Nat.card (towerKernelSlice Ξ e) * 2 ^ e := Nat.mul_le_mul_right _ h1

theorem towerOrd_le_card_mul {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    towerOrd Ξ e ≤ Nat.card (CharQuot Ξ) * 2 ^ e := by
  rw [towerOrd_eq_mul]
  exact Nat.mul_le_mul_right _ (Subgroup.card_le_card_group _)

/-- **Degree Stabilization (`ordAny`)**: The antitone kernel slice stabilizes at some `e₀`, so
`towerOrd Ξ e = c * 2 ^ e` for all `e ≥ e₀` with `1 ≤ c ≤ Nat.card (CharQuot Ξ)`. -/
theorem exists_ord_stabilizes {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) :
    ∃ c e0 : ℕ, 1 ≤ c ∧ c ≤ Nat.card (CharQuot Ξ) ∧
      ∀ e ≥ e0, towerOrd Ξ e = c * 2 ^ e := by
  let f : ℕ → ℕ := fun e => Nat.card (towerKernelSlice Ξ e)
  have hanti : Antitone f :=
    antitone_nat_of_succ_le (fun e => Subgroup.card_le_of_le (towerKernelSlice_succ_le Ξ e))
  have hne : (Set.range f).Nonempty := ⟨f 0, 0, rfl⟩
  obtain ⟨e0, he0⟩ : ∃ e0, f e0 = sInf (Set.range f) := Nat.sInf_mem hne
  refine ⟨f e0, e0, Nat.card_pos, Subgroup.card_le_card_group _, fun e he => ?_⟩
  rw [towerOrd_eq_mul]
  have hle : f e ≤ f e0 := hanti he
  have hge : f e0 ≤ f e := he0 ▸ Nat.sInf_le ⟨e, rfl⟩
  change f e * 2 ^ e = f e0 * 2 ^ e
  rw [le_antisymm hle hge]

/-- **Dyadic Window Covering (`anyFrame_window`)**: For every `e₀` and `W ≥ |CharQuot Ξ| * 2 ^ e₀`,
there exists a tower height `e ≥ e₀` with `W ≤ towerOrd Ξ e ≤ 2 * W`. -/
theorem exists_tower_level_in_window {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M))
    (e0 : ℕ) (W : ℝ) (hW : ((Nat.card (CharQuot Ξ) * 2 ^ e0 : ℕ) : ℝ) ≤ W) :
    ∃ e : ℕ, e0 ≤ e ∧ W ≤ (towerOrd Ξ e : ℝ) ∧ (towerOrd Ξ e : ℝ) ≤ 2 * W := by
  have hex : ∃ n : ℕ, W ≤ (towerOrd Ξ (e0 + n) : ℝ) := by
    obtain ⟨m, hm⟩ := exists_nat_gt W
    refine ⟨m, le_trans hm.le ?_⟩
    have h1 : m ≤ 2 ^ (e0 + m) := le_trans (Nat.lt_two_pow_self.le) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : 2 ^ (e0 + m) ≤ towerOrd Ξ (e0 + m) := two_pow_le_towerOrd Ξ (e0 + m)
    exact_mod_cast le_trans h1 h2
  classical
  let n := Nat.find hex
  have hn : W ≤ (towerOrd Ξ (e0 + n) : ℝ) := Nat.find_spec hex
  refine ⟨e0 + n, by omega, hn, ?_⟩
  cases hn' : n with
  | zero =>
    simp only [hn', Nat.add_zero] at hn ⊢
    have hle : (towerOrd Ξ e0 : ℝ) ≤ ((Nat.card (CharQuot Ξ) * 2 ^ e0 : ℕ) : ℝ) := by
      exact_mod_cast towerOrd_le_card_mul Ξ e0
    have h0 : (0 : ℝ) ≤ W := le_trans (Nat.cast_nonneg _) hW
    linarith
  | succ k =>
    have hlt : ¬ (W ≤ (towerOrd Ξ (e0 + k) : ℝ)) := Nat.find_min hex (by omega)
    push Not at hlt
    have hstep : (towerOrd Ξ (e0 + (k + 1)) : ℝ) ≤ 2 * (towerOrd Ξ (e0 + k) : ℝ) := by
      have := towerOrd_succ_le Ξ (e0 + k)
      have h' : e0 + (k + 1) = (e0 + k) + 1 := by omega
      rw [h']
      exact_mod_cast this
    linarith

/-! ## 3. Cyclotomic CM Host-Field Bridge (`IsChiField`) & Parity/Twist Tracking -/

/-- Minimal cyclotomic host-field datum carrying an embedded number field `E ↪ ℚ(ζ_{QS·q·d})`
and its Artin homomorphism `(ZMod (QS·q·d))ˣ →* G ≃ Gal(E/ℚ)`. -/
structure HostCyclotomicDatum (e : ℕ) where
  E : Type
  [field : Field E]
  [nf : NumberField E]
  QS : ℕ
  q : ℕ
  d : ℕ
  QS_pos : 0 < QS
  hyp : HostHyp q d
  tower_dvd : 2 ^ (e + 2) ∣ QS
  G : Type
  [grp : Group G]
  gal : (E ≃ₐ[ℚ] E) ≃* G
  cycEmb : E →ₐ[ℚ] CyclotomicField (QS * q * d) ℚ
  cycZeta : CyclotomicField (QS * q * d) ℚ
  cycZeta_prim : IsPrimitiveRoot cycZeta (QS * q * d)
  art : (ZMod (QS * q * d))ˣ →* G
  art_spec : ∀ (u : (ZMod (QS * q * d))ˣ)
      (τ : CyclotomicField (QS * q * d) ℚ ≃ₐ[ℚ] CyclotomicField (QS * q * d) ℚ),
      τ cycZeta = cycZeta ^ (u : ZMod (QS * q * d)).val →
      ∀ x : E, cycEmb (gal.symm (art u) x) = τ (cycEmb x)

attribute [instance] HostCyclotomicDatum.field HostCyclotomicDatum.nf HostCyclotomicDatum.grp

def HostCyclotomicDatum.condN {e : ℕ} (H : HostCyclotomicDatum e) : ℕ := H.QS * H.q * H.d

theorem HostCyclotomicDatum.condN_pos {e : ℕ} (H : HostCyclotomicDatum e) : 0 < H.condN :=
  Nat.mul_pos (Nat.mul_pos H.QS_pos H.hyp.q_prime.pos) H.hyp.d_prime.pos

/-- Exact Artin kernel specification `KerChi ψ e H` for a cyclotomic host datum `H`. -/
def KerChi (ψ : PChar) {e : ℕ} (H : HostCyclotomicDatum e) : Prop :=
  ψ.N ∣ H.QS ∧
  ∀ (a : ℕ) (h : a.Coprime H.condN),
    H.art (ZMod.unitOfCoprime a h) = 1 ↔
      (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧
        ψ.val a = 1 ∧ jacobiSym (a : ℤ) H.q = 1 ∧ jacobiSym (a : ℤ) H.d = 1

/-- Direct bridge from `KerChi` to `RHDirect.IsChiField` (matching `IsChiField.lean`). -/
theorem isChiField_of_kerChi (ψ : PChar) {e : ℕ} (H : HostCyclotomicDatum e)
    (h : KerChi ψ H) : IsChiField ψ e H.q H.d H.E := by
  obtain ⟨hψ, hart⟩ := h
  have hNpos : 0 < H.condN := H.condN_pos
  have : NeZero (H.QS * H.q * H.d) := ⟨hNpos.ne'⟩
  have hζ := H.cycZeta_prim
  refine ⟨H.QS * H.q * H.d, inferInstance, H.cycEmb, H.cycZeta, ?_, ?_, ?_, ?_, hζ, ?_⟩
  · exact dvd_trans H.tower_dvd (dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _))
  · exact dvd_trans hψ (dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _))
  · exact dvd_trans (dvd_mul_left _ _) (dvd_mul_right _ _)
  · exact dvd_mul_left _ _
  · intro τ a hτ
    have hprim : IsPrimitiveRoot (H.cycZeta ^ a) (H.QS * H.q * H.d) := by
      rw [← hτ]
      exact hζ.map_of_injective τ.injective
    have hcop : a.Coprime (H.QS * H.q * H.d) := (hζ.pow_iff_coprime hNpos a).mp hprim
    rw [← hart a hcop]
    set u := ZMod.unitOfCoprime a hcop with hu
    have hτu : τ H.cycZeta = H.cycZeta ^ (u : ZMod (H.QS * H.q * H.d)).val := by
      rw [hτ]
      have hv : (u : ZMod (H.QS * H.q * H.d)).val = a % (H.QS * H.q * H.d) := by
        rw [hu, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      rw [hv]
      conv_lhs => rw [← Nat.mod_add_div a (H.QS * H.q * H.d)]
      rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
    have hspec := H.art_spec u τ hτu
    constructor
    · intro hfix
      have hg : H.gal.symm (H.art u) = 1 := by
        ext x
        apply H.cycEmb.injective
        exact (hspec x).trans (hfix x)
      have h1 := congrArg H.gal hg
      rw [MulEquiv.apply_symm_apply, map_one] at h1
      exact h1
    · intro h1 x
      have h2 := hspec x
      rw [h1, map_one] at h2
      rw [← h2]
      rfl

/-- Jacobi symbol unit homomorphism `(ZMod p)ˣ →* ℤˣ` for an odd prime `p`. -/
def jacobiUnitHom (p : ℕ) (hp : p.Prime) : (ZMod p)ˣ →* ℤˣ where
  toFun u := if jacobiSym ((u : ZMod p).val : ℤ) p = 1 then 1 else -1
  map_one' := by
    have : Fact (1 < p) := ⟨hp.one_lt⟩
    change (if jacobiSym (((1 : (ZMod p)ˣ) : ZMod p).val : ℤ) p = 1 then (1 : ℤˣ) else -1) = 1
    rw [Units.val_one, ZMod.val_one, Nat.cast_one, jacobiSym.one_left, if_pos rfl]
  map_mul' u v := by
    have : NeZero p := ⟨hp.ne_zero⟩
    change (if jacobiSym (((u * v : (ZMod p)ˣ) : ZMod p).val : ℤ) p = 1 then (1 : ℤˣ) else -1) =
      (if jacobiSym ((u : ZMod p).val : ℤ) p = 1 then (1 : ℤˣ) else -1) *
      (if jacobiSym ((v : ZMod p).val : ℤ) p = 1 then (1 : ℤˣ) else -1)
    have hmod : ((u * v : (ZMod p)ˣ) : ZMod p).val ≡ (u : ZMod p).val * (v : ZMod p).val [MOD p] := by
      rw [Units.val_mul, ZMod.val_mul]
      exact Nat.mod_modEq _ _
    have hj : jacobiSym (((u * v : (ZMod p)ˣ) : ZMod p).val : ℤ) p =
        jacobiSym ((u : ZMod p).val : ℤ) p * jacobiSym ((v : ZMod p).val : ℤ) p := by
      rw [jacobiSym_congr_nat hmod, Nat.cast_mul, jacobiSym.mul_left]
    have hu := jacobiSym.eq_one_or_neg_one (a := ((u : ZMod p).val : ℤ)) (b := p)
      (by rw [Int.gcd_natCast_natCast]; exact ZMod.val_coe_unit_coprime u)
    have hv := jacobiSym.eq_one_or_neg_one (a := ((v : ZMod p).val : ℤ)) (b := p)
      (by rw [Int.gcd_natCast_natCast]; exact ZMod.val_coe_unit_coprime v)
    rw [hj]
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv] <;> norm_num

theorem jacobiUnitHom_val_eq_jacobiSym {p : ℕ} (hp : p.Prime) (u : (ZMod p)ˣ) :
    ((jacobiUnitHom p hp u : ℤˣ) : ℤ) = jacobiSym ((u : ZMod p).val : ℤ) p := by
  have hu := jacobiSym.eq_one_or_neg_one (a := ((u : ZMod p).val : ℤ)) (b := p)
    (by rw [Int.gcd_natCast_natCast]; exact ZMod.val_coe_unit_coprime u)
  unfold jacobiUnitHom
  dsimp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rcases hu with hu | hu <;> simp [hu]

/-- Explicit Artin homomorphism into `(ℤˣ × ℤˣ) × (HGrp e × CharQuot (zpowers ψ.χ))`
whose kernel is **exact** match with `IsChiField ψ e q d` (`KerChiAny`). -/
def artProdHom (ψ : PChar) (e q d : ℕ) (hH : HostHyp q d) :
    (ZMod (Nat.lcm (2 ^ (e + 2)) ψ.N * q * d))ˣ →*
      (ℤˣ × ℤˣ) × (HGrp e × CharQuot (Subgroup.zpowers ψ.χ)) :=
  let L := Nat.lcm (2 ^ (e + 2)) ψ.N
  have hLq : q ∣ L * q * d := dvd_trans (dvd_mul_left q L) (dvd_mul_right (L * q) d)
  have hLd : d ∣ L * q * d := dvd_mul_left d (L * q)
  have hLL : L ∣ L * q * d := dvd_trans (dvd_mul_right L q) (dvd_mul_right (L * q) d)
  MonoidHom.prod
    (MonoidHom.prod
      ((jacobiUnitHom q hH.q_prime).comp (ZMod.unitsMap hLq))
      ((jacobiUnitHom d hH.d_prime).comp (ZMod.unitsMap hLd)))
    ((etaMap (Subgroup.zpowers ψ.χ) e).comp (ZMod.unitsMap hLL))

/-- **Exact Artin-kernel characterization (`kerChiAny`)**: An element `a` coprime to
`lcm (2^(e+2)) ψ.N * q * d` lies in `ker (artProdHom ψ e q d hH)` iff it satisfies all four
congruence/character/Jacobi conditions of `RHDirect.IsChiField ψ e q d`. -/
theorem artProdHom_eq_one_iff (ψ : PChar) (e q d : ℕ) (hH : HostHyp q d) (a : ℕ)
    (h : a.Coprime (Nat.lcm (2 ^ (e + 2)) ψ.N * q * d)) :
    artProdHom ψ e q d hH (ZMod.unitOfCoprime a h) = 1 ↔
      (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧
        ψ.val a = 1 ∧ jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1 := by
  let L := Nat.lcm (2 ^ (e + 2)) ψ.N
  have hLq : q ∣ L * q * d := dvd_trans (dvd_mul_left q L) (dvd_mul_right (L * q) d)
  have hLd : d ∣ L * q * d := dvd_mul_left d (L * q)
  have hLL : L ∣ L * q * d := dvd_trans (dvd_mul_right L q) (dvd_mul_right (L * q) d)
  have hq_iff : jacobiUnitHom q hH.q_prime (ZMod.unitsMap hLq (ZMod.unitOfCoprime a h)) = 1 ↔
      jacobiSym (a : ℤ) q = 1 := by
    rw [← Units.val_inj, Units.val_one, jacobiUnitHom_val_eq_jacobiSym, unitsMap_unitOfCoprime,
      ZMod.coe_unitOfCoprime, ZMod.val_natCast, jacobiSym_congr_nat (Nat.mod_modEq a q)]
  have hd_iff : jacobiUnitHom d hH.d_prime (ZMod.unitsMap hLd (ZMod.unitOfCoprime a h)) = 1 ↔
      jacobiSym (a : ℤ) d = 1 := by
    rw [← Units.val_inj, Units.val_one, jacobiUnitHom_val_eq_jacobiSym, unitsMap_unitOfCoprime,
      ZMod.coe_unitOfCoprime, ZMod.val_natCast, jacobiSym_congr_nat (Nat.mod_modEq a d)]
  have h2_iff : hclL ψ.N e (ZMod.unitsMap hLL (ZMod.unitOfCoprime a h)) = 1 ↔
      (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) := by
    rw [hclL, MonoidHom.comp_apply, unitsMap_unitsMap, unitsMap_unitOfCoprime, hcl_nat_eq_one_iff]
  have hψ_iff : xiL (Subgroup.zpowers ψ.χ) e (ZMod.unitsMap hLL (ZMod.unitOfCoprime a h)) = 1 ↔
      ψ.val a = 1 := by
    rw [xiL, MonoidHom.comp_apply, charQuotMk_zpowers_eq_one_iff, unitsMap_unitsMap,
      unitsMap_unitOfCoprime, ZMod.coe_unitOfCoprime]
    rfl
  unfold artProdHom
  simp only [MonoidHom.prod_apply, Prod.mk_eq_one, MonoidHom.comp_apply, etaMap]
  rw [hq_iff, hd_iff, h2_iff, hψ_iff]
  tauto

/-- Quadratic twist function `tw f q d i j a := f a * (a|q)^i * (a|d)^j` (`TwistForm`). -/
def quadTwist (f : ℕ → ℂ) (q d : ℕ) (i j : Fin 2) (a : ℕ) : ℂ :=
  f a * ((jacobiSym (a : ℤ) q : ℤ) : ℂ) ^ (i : ℕ) * ((jacobiSym (a : ℤ) d : ℤ) : ℂ) ^ (j : ℕ)

/-- Every real primitive Dirichlet character has order dividing `2` (`ψ.χ ^ 2 = 1`). -/
theorem real_pchar_sq_eq_one {ψ : PChar} (hr : ψ.IsReal) : ψ.χ ^ 2 = 1 := by
  ext u
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  have h1 := DirichletCharacter.unit_norm_eq_one ψ.χ u
  have h2 : (starRingEnd ℂ) (ψ.χ u) = ψ.χ u := Complex.conj_eq_iff_im.2 (hr u)
  calc ψ.χ u ^ 2 = ψ.χ u * (starRingEnd ℂ) (ψ.χ u) := by rw [h2, sq]
    _ = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; norm_num

/-- A real primitive Dirichlet character is self-inverse (`ψ.inv = ψ`). -/
theorem real_pchar_inv_eq_self {ψ : PChar} (hr : ψ.IsReal) : ψ.inv = ψ := by
  have hsq : ψ.χ ^ 2 = 1 := real_pchar_sq_eq_one hr
  have hinv : ψ.χ⁻¹ = ψ.χ := by
    have h1 : ψ.χ⁻¹ * (ψ.χ * ψ.χ) = ψ.χ⁻¹ * 1 := by rw [← sq, hsq]
    rw [← mul_assoc, inv_mul_cancel, one_mul, mul_one] at h1
    exact h1.symm
  cases ψ
  simp only [PChar.inv]
  congr 1

/-- Parity tracking for `PChar`: every primitive character is either even (`χ (-1) = 1`) or odd
(`χ (-1) = -1`), and `inv` preserves parity. -/
theorem pchar_even_or_odd (ψ : PChar) : ψ.χ.Even ∨ ψ.χ.Odd :=
  DirichletCharacter.even_or_odd ψ.χ

theorem pchar_even_iff_inv_even (ψ : PChar) : ψ.χ.Even ↔ ψ.inv.χ.Even := by
  change ψ.χ (-1) = 1 ↔ ψ.χ⁻¹ (-1) = 1
  have hinv : ψ.χ⁻¹ (-1 : ZMod ψ.N) = (ψ.χ (-1 : ZMod ψ.N))⁻¹ := by
    have hu : (-1 : ZMod ψ.N) = ((-1 : (ZMod ψ.N)ˣ) : ZMod ψ.N) := by simp
    rw [hu, mulChar_inv_apply_unit]
  rw [hinv, inv_eq_one]

/-- Parity sign of the Jacobi twist `(·|q)` for `q ≡ 3 (mod 4)`: `jacobiSym (-1) q = -1`. -/
theorem jacobiSym_neg_one_of_mod_four_eq_three {q : ℕ} (hq : q % 4 = 3) :
    jacobiSym (-1 : ℤ) q = -1 := by
  rw [jacobiSym.at_neg_one (Nat.odd_iff.2 (by omega)), ZMod.χ₄_nat_three_mod_four hq]

/-- Parity tracking for `quadTwist`: twisting an arbitrary character `ξ` by `(·|q)^i (·|d)^j`
for `q ≡ 3 (mod 8)` and `d ≡ 7 (mod 16)` multiplies its parity sign by `(-1)^(i + j)`. -/
theorem quadTwist_parity_sign {q d : ℕ} (hH : HostHyp q d) (i j : Fin 2) :
    ((jacobiSym (-1 : ℤ) q : ℤ) : ℂ) ^ (i : ℕ) *
      ((jacobiSym (-1 : ℤ) d : ℤ) : ℂ) ^ (j : ℕ) = (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) := by
  have hq4 : q % 4 = 3 := by have := hH.q_mod; omega
  have hd4 : d % 4 = 3 := by have := hH.d_mod; omega
  rw [jacobiSym_neg_one_of_mod_four_eq_three hq4, jacobiSym_neg_one_of_mod_four_eq_three hd4]
  push_cast
  rw [← pow_add]

/-- Every odd prime dividing a character's conductor `N ∣ S * q * d` (`q, d` distinct odd primes
coprime to `S`) divides `ordCompl[2] S * q * d`. -/
theorem odd_prime_dvd_conductor_split {N S q d p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hNdvd : N ∣ S * q * d) (hpN : p ∣ N) :
    p ∣ ordCompl[2] S * q * d := by
  have h := hpN.trans hNdvd
  rcases (hp.dvd_mul).1 h with h | h
  · rcases (hp.dvd_mul).1 h with h | h
    · refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ q) d
      have hc2 : p.Coprime (2 ^ S.factorization 2) :=
        ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right _
      refine Nat.Coprime.dvd_of_dvd_mul_left hc2 ?_
      rw [Nat.ordProj_mul_ordCompl_eq_self]
      exact h
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) d
  · exact Dvd.dvd.mul_left h _

/-! ## 4. `WinPair` / `PageN` Window Covering & `401 = 400 + 1` Scaling (`WinPairs`) -/

/-- Auxiliary prime-pair supply predicate at modulus `M` (`PairEx` without dead fields). -/
def PairSupply : Prop :=
  ∀ (M : ℕ), 0 < M → ∀ eps A : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ A →
    ∃ Y1 : ℝ, ∀ Y ≥ Y1, ∃ q d : ℕ, WinPair eps Y q d ∧ Nat.Coprime M (q * d)

/-- Pointwise window datum at scale `x` produced from `VWinAt S ψ 401` and `PairSupply`. -/
structure WinDatum (S : SelmerSystem) (ψ : PChar) (eps J c x Y : ℝ) (q d e : ℕ) : Prop where
  lo : x ^ (1 / J) ≤ Y
  up : Y ≤ x
  pair : WinPair eps Y q d
  coprime : Nat.Coprime ψ.N (q * d)
  n_lo : x ^ (2 + 8 * eps) ≤ c * (2 : ℝ) ^ e
  n_up : c * (2 : ℝ) ^ e ≤ 2 * x ^ (2 + 8 * eps)
  bound : ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E →
    VVle S E ⌊x ^ (400 : ℝ)⌋₊ (Real.sqrt (Real.exp (x ^ eps)))

/-- **`401 = 400 + 1` Window-Covering & Rescaling Theorem (`winPairs`)**:
Converts `VWinAt S ψ 401` (with `W ≤ x ≤ W²`) and `PairSupply` into a complete `[Z, Z^(3/2)]`
multiplicative window covered by `c * 2^e ∈ [x^(2+8ε), 2 x^(2+8ε)]` and Selmer cutoff `⌊x^400⌋₊`. -/
theorem winPairs_supply (S : SelmerSystem) (ψ : PChar) (eps c : ℝ)
    (heps : 0 < eps) (heps52 : eps < 1 / 52) (hc : 1 ≤ c)
    (hV : VWinAt S ψ 401) (hP : PairSupply) :
    ∃ J : ℝ, 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧
      ∀ x : ℝ, Z ≤ x → x ≤ Z ^ ((3 : ℝ) / 2) →
        ∃ (Y : ℝ) (q d e : ℕ), WinDatum S ψ eps J c x Y q d e := by
  obtain ⟨e, he⟩ := exists_pageN eps heps
  obtain ⟨J, hJ, X0, hX0⟩ := hV eps heps heps52 e he
  have hN : 0 < ψ.N := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨Y1, hY1⟩ := hP ψ.N hN eps J heps heps52 hJ
  have ha : 0 < 2 + 8 * eps := by linarith
  have hc0 : 0 ≤ c := by linarith
  obtain ⟨k, hk1, hka⟩ : ∃ k : ℝ, 1 ≤ k ∧ k ^ (2 + 8 * eps) = c := by
    refine ⟨c ^ (1 / (2 + 8 * eps)), Real.one_le_rpow hc (one_div_nonneg.2 ha.le), ?_⟩
    rw [one_div, Real.rpow_inv_rpow hc0 ha.ne']
  have hk0 : 0 ≤ k := by linarith
  refine ⟨J, hJ, fun y => ?_⟩
  have hJ0 : J ≠ 0 := ne_of_gt (by linarith)
  have hJi : 0 ≤ 1 / J := one_div_nonneg.2 (by linarith)
  obtain ⟨M, hM1, hMy, hMY1, hMk3, hMk400⟩ : ∃ M : ℝ, 1 ≤ M ∧ y ≤ M ∧ Y1 ≤ M ∧
      k ^ (3 : ℝ) ≤ M ∧ k ^ (400 : ℝ) ≤ M :=
    ⟨max 1 (max y (max Y1 (max (k ^ (3 : ℝ)) (k ^ (400 : ℝ))))),
      by simp, by simp, by simp, by simp, by simp⟩
  obtain ⟨X, hXX0, hXM⟩ : ∃ X : ℝ, X0 ≤ X ∧ M ^ J ≤ X :=
    ⟨max X0 (M ^ J), le_max_left _ _, le_max_right _ _⟩
  have hM0 : 0 ≤ M := by linarith
  have hX1 : 1 ≤ X := (Real.one_le_rpow hM1 (by linarith)).trans hXM
  have hX0' : 0 ≤ X := by linarith
  have hY0M : M ≤ X ^ (1 / J) := by
    calc M = (M ^ J) ^ (1 / J) := by rw [one_div, Real.rpow_rpow_inv hM0 hJ0]
      _ ≤ X ^ (1 / J) := Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) hXM hJi
  obtain ⟨q, d, hpair, hcop⟩ := hY1 (X ^ (1 / J)) (hMY1.trans hY0M)
  obtain ⟨W, hW0, hW2, hWV⟩ := hX0 X hXX0 q d hpair
  have hWM : M ≤ W := hY0M.trans hW0
  have hW1 : 1 ≤ W := hM1.trans hWM
  have hWnn : 0 ≤ W := by linarith
  have hk3 : k ^ (3 : ℝ) ≤ W := hMk3.trans hWM
  have hlem : (k * W) ^ ((3 : ℝ) / 2) ≤ W ^ (2 : ℝ) := by
    have h1 : (k * W) ^ ((3 : ℝ) / 2) = ((k * W) ^ (3 : ℝ)) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul (mul_nonneg hk0 hWnn)]
      norm_num
    have h2 : W ^ (2 : ℝ) = (W ^ (4 : ℝ)) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul hWnn]
      norm_num
    rw [h1, h2]
    apply Real.rpow_le_rpow (Real.rpow_nonneg (mul_nonneg hk0 hWnn) _) _ (by norm_num)
    rw [Real.mul_rpow hk0 hWnn, show (4 : ℝ) = 1 + 3 by norm_num,
      Real.rpow_add (by linarith : 0 < W), Real.rpow_one]
    exact mul_le_mul_of_nonneg_right hk3 (Real.rpow_nonneg hWnn _)
  refine ⟨k * W, hMy.trans (hWM.trans (le_mul_of_one_le_left hWnn hk1)), fun x hZx hxZ => ?_⟩
  have hkpos : 0 < k := by linarith
  have hxW2 : x ≤ W ^ (2 : ℝ) := hxZ.trans hlem
  have hxX : x ≤ X := hxW2.trans hW2
  have hx1 : W ≤ x := (le_mul_of_one_le_left hWnn hk1).trans hZx
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨x', rfl⟩ : ∃ x', x = k * x' := ⟨x / k, by field_simp⟩
  have hWx' : W ≤ x' := le_of_mul_le_mul_left hZx hkpos
  have hx'0 : 0 ≤ x' := hWnn.trans hWx'
  have hx'1 : 1 ≤ x' := hW1.trans hWx'
  have hx'x : x' ≤ k * x' := le_mul_of_one_le_left hx'0 hk1
  have hpage := he x' hx'1
  have hpow : (k * x') ^ (2 + 8 * eps) = c * x' ^ (2 + 8 * eps) := by
    rw [Real.mul_rpow hk0 hx'0, hka]
  refine ⟨X ^ (1 / J), q, d, e x', ?_, ?_, hpair, hcop, ?_, ?_, ?_⟩
  · exact Real.rpow_le_rpow hx0 hxX hJi
  · exact hW0.trans hx1
  · rw [hpow]
    exact mul_le_mul_of_nonneg_left hpage.1 hc0
  · rw [hpow]
    calc c * (2 : ℝ) ^ (e x') ≤ c * (2 * x' ^ (2 + 8 * eps)) :=
          mul_le_mul_of_nonneg_left hpage.2 hc0
      _ = 2 * (c * x' ^ (2 + 8 * eps)) := by ring
  · intro E _ _ hE
    have hv := hWV x' hWx' (hx'x.trans hxW2) E hE
    refine hv.mono ?_ ?_
    · apply Nat.floor_mono
      rw [Real.mul_rpow hk0 hx'0, show (401 : ℝ) = 1 + 400 by norm_num,
        Real.rpow_add (by linarith : 0 < x'), Real.rpow_one]
      exact mul_le_mul_of_nonneg_right (hMk400.trans (hWM.trans hWx')) (Real.rpow_nonneg hx'0 _)
    · exact Real.sqrt_le_sqrt (Real.exp_le_exp.2 (Real.rpow_le_rpow hx'0 hx'x heps.le))

/-! ## 5. Short Norms, Small Primes ≡ 1 (mod M), Coprime Level Primes & Large-Scale Bounds -/

/-- Linnik-type polynomial bound for the least prime `p ≡ 1 (mod M)` (`SmallOne`). -/
def SmallOne : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧ ∀ M : ℕ, 2 ≤ M → ∃ p : ℕ, p.Prime ∧ p % M = 1 ∧ (p : ℝ) ≤ (M : ℝ) ^ A

private theorem mod_eq_one_of_mod_mul {p M K : ℕ} (h : p % (M * K) = 1) (hM : 1 < M) :
    p % M = 1 := by
  rw [← Nat.mod_mul_right_mod p M K, h, Nat.mod_eq_of_lt hM]

/-- **Three Distinct Auxiliary Primes (`exists_three_primes_one_mod_le_rpow`)**:
From `SmallOne`, produces three distinct primes `p, p', q0 ≤ N ^ C8` with `p ≡ p' ≡ 1 (mod 15N)`
and `q0 ≡ 1 (mod N)`, all coprime to `N`. -/
theorem exists_three_primes_one_mod_le_rpow (hS : SmallOne) :
    ∃ C8 : ℝ, 1 ≤ C8 ∧ ∀ N : ℕ, 30 ≤ N →
      ∃ p p' q0 : ℕ,
        p.Prime ∧ p'.Prime ∧ q0.Prime ∧ p ≠ p' ∧ q0 ≠ p ∧ q0 ≠ p' ∧
        p % (15 * N) = 1 ∧ p' % (15 * N) = 1 ∧ q0 % N = 1 ∧
        (p : ℝ) ≤ (N : ℝ) ^ C8 ∧ (p' : ℝ) ≤ (N : ℝ) ^ C8 ∧ (q0 : ℝ) ≤ (N : ℝ) ^ C8 := by
  obtain ⟨A, hA1, hA⟩ := hS
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hAA : A ≤ A * A := by nlinarith
  have hAAA : 0 ≤ A * A * A := by positivity
  refine ⟨(1 + (2 * A + (2 * A + 2) * A)) * A, by nlinarith, ?_⟩
  intro N hN
  have hx : (30 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hx1 : (1 : ℝ) ≤ N := by linarith
  have key : ∀ (M : ℕ) (e : ℝ), 2 ≤ M → (M : ℝ) ≤ (N : ℝ) ^ e →
      ∃ q : ℕ, q.Prime ∧ q % M = 1 ∧ (q : ℝ) ≤ (N : ℝ) ^ (e * A) := by
    intro M e hM hle
    obtain ⟨q, hq, hqm, hqle⟩ := hA M hM
    refine ⟨q, hq, hqm, le_trans hqle ?_⟩
    rw [Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hle hA0
  obtain ⟨p, hp, hpm, hple⟩ := key (15 * N) 2 (by omega) (by
    push_cast
    rw [Real.rpow_two]
    nlinarith)
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨p', hp', hp'm, hp'le⟩ := key (p * (15 * N)) (2 * A + 2)
    (by
      have := Nat.mul_le_mul hp.two_le (show 1 ≤ 15 * N by omega)
      omega)
    (by
      push_cast
      rw [Real.rpow_add hx0, Real.rpow_two]
      exact mul_le_mul hple (by nlinarith) (by positivity) (by positivity))
  obtain ⟨q0, hq0, hq0m, hq0le⟩ := key (N * (p * p')) (1 + (2 * A + (2 * A + 2) * A))
    (by
      have := Nat.mul_le_mul (show 2 ≤ N by omega) (Nat.mul_pos hp.pos hp'.pos)
      omega)
    (by
      push_cast
      rw [Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_one]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hple hp'le (Nat.cast_nonneg _) (by positivity)) hx0.le)
  have hp'p : p' % p = 1 := mod_eq_one_of_mod_mul hp'm hp1
  have hp'15 : p' % (15 * N) = 1 :=
    mod_eq_one_of_mod_mul (K := p) (by rw [Nat.mul_comm]; exact hp'm) (by omega)
  have hq0N : q0 % N = 1 := mod_eq_one_of_mod_mul hq0m (by omega)
  have hq0p : q0 % p = 1 :=
    mod_eq_one_of_mod_mul (K := p' * N)
      (by rw [show p * (p' * N) = N * (p * p') by ring]; exact hq0m) hp1
  have hq0p' : q0 % p' = 1 :=
    mod_eq_one_of_mod_mul (K := p * N)
      (by rw [show p' * (p * N) = N * (p * p') by ring]; exact hq0m) hp'.one_lt
  refine ⟨p, p', q0, hp, hp', hq0, ?_, ?_, ?_, hpm, hp'15, hq0N, ?_, ?_, hq0le⟩
  · intro h
    rw [← h, Nat.mod_self] at hp'p
    omega
  · intro h
    rw [h, Nat.mod_self] at hq0p
    omega
  · intro h
    rw [h, Nat.mod_self] at hq0p'
    omega
  · exact hple.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith))
  · exact hp'le.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith))

/-- Unconditional existence of four distinct level primes `a, b, c, d > QS` coprime to `QS`
with `c ≡ 1 (mod 15)` and `d ≡ 1 (mod 15)` (`nonempty_choices` in `SecondSetNoRelation.lean`). -/
theorem exists_four_coprime_level_primes (QS : ℕ) (hQS : 0 < QS) :
    ∃ a b c d : ℕ,
      a.Prime ∧ b.Prime ∧ c.Prime ∧ d.Prime ∧
      a < b ∧ b < c ∧ c < d ∧
      Nat.Coprime a QS ∧ Nat.Coprime b QS ∧ Nat.Coprime c QS ∧ Nat.Coprime d QS ∧
      c ≡ 1 [MOD 15] ∧ d ≡ 1 [MOD 15] := by
  obtain ⟨a, hla, ha⟩ := Nat.exists_infinite_primes (QS + 1)
  obtain ⟨b, hlb, hb⟩ := Nat.exists_infinite_primes (a + 1)
  obtain ⟨c, hc, hbc, hc1⟩ := Nat.exists_prime_gt_modEq_one (k := 15) b (by norm_num)
  obtain ⟨d, hd, hcd, hd1⟩ := Nat.exists_prime_gt_modEq_one (k := 15) c (by norm_num)
  have cop : ∀ p : ℕ, p.Prime → QS < p → Nat.Coprime p QS := fun p hp hlt =>
    (Nat.Prime.coprime_iff_not_dvd hp).2
      (fun hdv => absurd (Nat.le_of_dvd hQS hdv) (by omega))
  exact ⟨a, b, c, d, ha, hb, hc, hd, by omega, hbc, hcd,
    cop a ha (by omega), cop b hb (by omega), cop c hc (by omega), cop d hd (by omega),
    hc1, hd1⟩

/-- Asymptotic dominance `C * log x ≤ x ^ a` for any `a > 0, C > 0`. -/
theorem mul_log_le_rpow_eventually (a C : ℝ) (ha : 0 < a) (hC : 0 < C) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → C * Real.log x ≤ x ^ a := by
  have h := (isLittleO_log_rpow_atTop ha).bound (show (0 : ℝ) < 1 / C by positivity)
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.mp h
  refine ⟨max x1 1, fun x hx => ?_⟩
  have hx1' := hx1 x (le_trans (le_max_left _ _) hx)
  have hxone : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hpow : 0 ≤ x ^ a := Real.rpow_nonneg (by linarith) a
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hpow] at hx1'
  calc C * Real.log x ≤ C * (1 / C * x ^ a) := by gcongr
    _ = x ^ a := by field_simp

/-- Asymptotic conductor-log dominance `3 * x^(ε/5) * (log x)^2 * C < x^ε` (`levelData.lean`). -/
theorem mod_log_small_eventually (C eps : ℝ) (hC : 1 ≤ C) (he : 0 < eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, 3 * x ^ (eps / 5) * Real.log x ^ 2 * C < x ^ eps := by
  have hc : 0 < 1 / (4 * C) := by positivity
  have h1 := (isLittleO_log_rpow_atTop (show 0 < eps / 5 by positivity)).bound hc
  obtain ⟨x0, hx⟩ := Filter.eventually_atTop.1 (h1.and (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨x0, fun x hxx => ?_⟩
  obtain ⟨ha, hb⟩ := hx x hxx
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _),
    abs_of_nonneg hl0] at ha
  have hu : 1 ≤ x ^ (eps / 5) := Real.one_le_rpow hb (by positivity)
  have he5 : x ^ eps = (x ^ (eps / 5)) ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    push_cast
    ring
  rw [he5]
  generalize x ^ (eps / 5) = u at ha hu ⊢
  generalize Real.log x = l at ha hl0 ⊢
  have h2 : 4 * C * l ≤ u := by
    have := mul_le_mul_of_nonneg_left ha (show 0 ≤ 4 * C by positivity)
    rwa [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
  have h3 : l ≤ u := by nlinarith
  have h4 : 4 * C * l * l ≤ u * u := mul_le_mul h2 h3 hl0 (by linarith)
  have h5 : u ^ 3 ≤ u ^ 5 := pow_le_pow_right₀ hu (by norm_num)
  have h6 : 0 < u ^ 3 := by positivity
  have h7 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ u by linarith)
  nlinarith

/-- Polynomial-conductor bound `(N : ℝ) ^ C < exp (x ^ eps)` from `log N ≤ 3 x^(ε/5) (log x)^2`. -/
theorem rpow_lt_exp_of_log_le {x eps C : ℝ} {N : ℕ} (hN : 0 < N) (hC : 0 ≤ C)
    (hlog : Real.log (N : ℝ) ≤ 3 * x ^ (eps / 5) * Real.log x ^ 2)
    (hdom : 3 * x ^ (eps / 5) * Real.log x ^ 2 * C < x ^ eps) :
    (N : ℝ) ^ C < Real.exp (x ^ eps) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_def_of_pos hNpos]
  exact Real.exp_lt_exp.2 ((mul_le_mul_of_nonneg_right hlog hC).trans_lt hdom)

/-- **Large-Scale Auxiliary Prime Dominance (`qdBig` in `MulLogLeRpowEventually.lean`)**:
Under `WinPair eps Y q d` with `x ^ (1 / C0) ≤ Y`, `r ≤ x ^ 5`, and `t ≤ x ^ 401`, for all
sufficiently large `x` we have `4 * t * r + 1 < q`, `4 * t * r + 1 < d`, and `100 ≤ d`. -/
theorem qd_gt_rank_product_eventually (eps C0 : ℝ) (he0 : 0 < eps) :
    ∃ x0 : ℝ, ∀ (x Y : ℝ) (q d r t : ℕ), x0 ≤ x →
      x ^ (1 / max C0 1) ≤ Y →
      (r : ℝ) ≤ x ^ (5 : ℕ) →
      (t : ℝ) ≤ x ^ (401 : ℕ) →
      WinPair eps Y q d →
      (4 * t * r + 1 < q ∧ 4 * t * r + 1 < d) ∧ 100 ≤ d := by
  have hC1pos : 0 < max C0 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨x2, hx2⟩ := mul_log_le_rpow_eventually (eps / 5 / max C0 1) 814 (by positivity) (by norm_num)
  refine ⟨max x2 6, fun x Y q d r t hx hYlo hr5 ht401 hW => ?_⟩
  have hxx2 : x2 ≤ x := le_trans (le_max_left _ _) hx
  have hx6 : (6 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hYe : x ^ (eps / 5 / max C0 1) ≤ Y ^ (eps / 5) := by
    have h : x ^ (eps / 5 / max C0 1) = (x ^ (1 / max C0 1)) ^ (eps / 5) := by
      rw [← Real.rpow_mul hx0.le]
      congr 1
      field_simp
    rw [h]
    exact Real.rpow_le_rpow (by positivity) hYlo (by positivity)
  have hlogx := hx2 x hxx2
  have hqlog : 407 * Real.log x < Real.log q := by linarith [hW.q_lo]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hW.q_prime.pos
  have hqbig : x ^ (407 : ℕ) < (q : ℝ) := by
    rw [← Real.log_lt_log_iff (by positivity) hq0, Real.log_pow]
    push_cast
    linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have htr : (t : ℝ) * r ≤ x ^ 401 * x ^ 5 := mul_le_mul ht401 hr5 hr0 (by positivity)
  have e1 : x ^ 401 * x ^ 5 = x ^ 406 := by ring
  have e2 : x ^ 407 = x * x ^ 406 := by ring
  have h3 : (216 : ℝ) ≤ x ^ 406 := by
    have a1 : x ^ 3 ≤ x ^ 406 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have a2 : (6 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx6 3
    norm_num at a2
    linarith
  have h4 : 6 * x ^ 406 ≤ x * x ^ 406 := mul_le_mul_of_nonneg_right hx6 (by positivity)
  have hqR : ((4 * t * r + 2 : ℕ) : ℝ) < q := by
    push_cast
    nlinarith
  have hqR' : ((102 : ℕ) : ℝ) < q := by
    push_cast
    nlinarith
  have hqN : 4 * t * r + 2 < q := by exact_mod_cast hqR
  have hqN' : 102 < q := by exact_mod_cast hqR'
  have hqd : q ≤ d + 1 := Nat.le_of_dvd (Nat.succ_pos _) hW.d_q
  generalize 4 * t * r = P at *
  omega

/-- In any number field `K`, the ideal `(m)` in `𝓞 K` is proper for every integer `m > 1`. -/
theorem span_natCast_ne_top_of_one_lt (K : Type) [Field K] [NumberField K] (m : ℕ) (hm : 1 < m) :
    Ideal.span {(m : 𝓞 K)} ≠ ⊤ := by
  intro h
  have hu : IsUnit (m : 𝓞 K) := Ideal.span_singleton_eq_top.mp h
  have hn := hu.map (Algebra.norm ℤ (S := 𝓞 K))
  rw [show (m : 𝓞 K) = algebraMap ℤ (𝓞 K) (m : ℤ) by simp, Algebra.norm_algebraMap] at hn
  have hd : Module.finrank ℤ (𝓞 K) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff hd, Int.isUnit_iff] at hn
  omega

/-! ## 6. Cyclic Level Cardinality, Parity & Unified Host-Field Supply Assembly -/

/-- The cyclic level size `(Level.cyc ψ).o` is bounded by `Nat.totient ψ.N`. -/
theorem cyc_o_le_totient (ψ : PChar) : (Level.cyc ψ).o ≤ Nat.totient ψ.N := by
  change Nat.card (Subgroup.zpowers ψ.χ) ≤ Nat.totient ψ.N
  rw [Nat.card_zpowers]
  have hpow : ψ.χ ^ Nat.totient ψ.N = 1 := by
    ext u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val,
      ← ZMod.card_units_eq_totient ψ.N, ← Nat.card_eq_fintype_card, pow_card_eq_one',
      Units.val_one, map_one]
  exact Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne ψ.N)))
    (orderOf_dvd_of_pow_eq_one hpow)

/-- The number of kept primitive characters in `Level.cyc ψ` is at most `(Level.cyc ψ).o`. -/
theorem cyc_KEPT_card_le (ψ : PChar) : (Level.cyc ψ).KEPT.card ≤ (Level.cyc ψ).o := by
  classical
  change ((Finset.univ.filter fun χ : DirichletCharacter ℂ ψ.N =>
      χ ∈ Subgroup.zpowers ψ.χ).image PChar.of).card ≤ Nat.card (Subgroup.zpowers ψ.χ)
  refine (Finset.card_image_le).trans ?_
  rw [Nat.card_eq_fintype_card]
  have hcard : (Finset.univ.filter fun χ : DirichletCharacter ℂ ψ.N =>
      χ ∈ Subgroup.zpowers ψ.χ).card = Fintype.card (Subgroup.zpowers ψ.χ) := by
    rw [Fintype.card_subtype]
  exact hcard.le

/-- Every character in `Subgroup.zpowers ψ.χ` is even iff `ψ.χ` itself is even. -/
theorem all_even_zpowers_iff (ψ : PChar) :
    (∀ χ ∈ Subgroup.zpowers ψ.χ, χ.Even) ↔ ψ.χ.Even := by
  constructor
  · intro h
    exact h ψ.χ (Subgroup.mem_zpowers ψ.χ)
  · intro h χ hχ
    rw [Subgroup.zpowers_eq_closure] at hχ
    induction hχ using Subgroup.closure_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      rwa [hx]
    | one =>
      show (1 : DirichletCharacter ℂ ψ.N) (-1) = 1
      have hu : (-1 : ZMod ψ.N) = ((-1 : (ZMod ψ.N)ˣ) : ZMod ψ.N) := by simp
      rw [hu, MulChar.one_apply_coe]
    | mul x y _ _ hx hy =>
      show (x * y) (-1) = 1
      rw [MulChar.mul_apply, hx, hy, mul_one]
    | inv x _ hx =>
      show x⁻¹ (-1) = 1
      have hu : (-1 : ZMod ψ.N) = ((-1 : (ZMod ψ.N)ˣ) : ZMod ψ.N) := by simp
      rw [hu, mulChar_inv_apply_unit, ← hu]
      change x (-1) = 1 at hx
      rw [hx, inv_one]

/-- A real primitive character generates a cyclic level of order at most `2`. -/
theorem cyc_o_le_two_of_isReal {ψ : PChar} (hr : ψ.IsReal) : (Level.cyc ψ).o ≤ 2 := by
  change Nat.card (Subgroup.zpowers ψ.χ) ≤ 2
  rw [Nat.card_zpowers]
  have hsq : ψ.χ ^ 2 = 1 := real_pchar_sq_eq_one hr
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hsq)

/-- **Unified Host-Field Supply Assembly**:
Combines cyclotomic 2-tower stabilization (`exists_ord_stabilizes`), CRT conductor divisibility
(`primitive_conductor_dvd_QS`), `WinPair` reciprocity (`winPair_reciprocity`), `401 = 400 + 1`
window covering (`winPairs_supply`), and the `IsChiField` Artin-kernel bridge
(`isChiField_of_kerChi`) for any primitive character `ψ : PChar`. -/
theorem hostFieldSupply_assembly (S : SelmerSystem) (ψ : PChar)
    (hV : VWinAt S ψ 401) (hP : PairSupply) :
    ∃ c e0 : ℕ, 1 ≤ c ∧
      (∀ e ≥ e0, towerOrd (Subgroup.zpowers ψ.χ) e = c * 2 ^ e ∧
        ψ.N ∣ QS (Subgroup.zpowers ψ.χ) e ∧
        QS (Subgroup.zpowers ψ.χ) e ≤ 4 * ψ.N * 2 ^ e) ∧
      ∀ eps : ℝ, 0 < eps → eps < 1 / 52 →
        ∃ J : ℝ, 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧
          ∀ x : ℝ, Z ≤ x → x ≤ Z ^ ((3 : ℝ) / 2) →
            ∃ (Y : ℝ) (q d e : ℕ),
              WinDatum S ψ eps J (c : ℝ) x Y q d e ∧ HostHyp q d := by
  obtain ⟨c, e0, hc1, _, hstab⟩ := exists_ord_stabilizes (Subgroup.zpowers ψ.χ)
  refine ⟨c, e0, hc1, fun e he => ⟨hstab e he, primitive_conductor_dvd_QS ψ.χ ψ.prim e,
    QS_le_mul (Subgroup.zpowers ψ.χ) e⟩, fun eps heps heps52 => ?_⟩
  have hcr : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  obtain ⟨J, hJ, hwin⟩ := winPairs_supply S ψ eps (c : ℝ) heps heps52 hcr hV hP
  refine ⟨J, hJ, fun y => ?_⟩
  obtain ⟨Z, hZy, hZ⟩ := hwin y
  refine ⟨Z, hZy, fun x hZx hxZ => ?_⟩
  obtain ⟨Y, q, d, e, hdat⟩ := hZ x hZx hxZ
  exact ⟨Y, q, d, e, hdat, (winPair_reciprocity hdat.pair).1⟩

end HostFieldSupply

end RHDirect

end
