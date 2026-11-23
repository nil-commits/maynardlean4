import RHDirect.Interfaces
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# RHDirect.ElementaryEquiv

Compact, self-contained, 0-`sorry`, 0-axiom statement sanity checks, exact bidirectional
equivalences, zero symmetries, trivial-zero characterization, and elementary Chebyshev /
von Mangoldt / Robin–Lagarias bridge lemmas for the 5 headline RH/GRH theorems in
`RHDirect.Interfaces`.

## Contents
1. **Conjugation & Functional-Equation Symmetries**
   - `LSeries_conj`, `LFunction_conj`, `riemannZeta_conj`
   - Four-fold symmetry of critical-strip zeros of `ζ(s)` (`s`, `conj s`, `1 - s`, `1 - conj s`)
   - Critical-strip zero symmetries of primitive `L(χ, s)` (`s ↦ conj s` and `s ↦ 1 - s` swap
     `χ ↔ χ⁻¹`, so reflection across `Re(s) = 1/2`, `s ↦ 1 - conj s`, preserves `χ`)
2. **Trivial-Zero Characterization & Exact RH Equivalences**
   - `riemannZeta_eq_zero_of_re_nonpos_iff`: on `Re(s) ≤ 0`, `ζ(s) = 0 ↔ ∃ n : ℕ, s = -2*(n+1)`
   - `riemannZeta_nontrivial_zero_mem_strip`: every nontrivial zero satisfies `0 < Re(s) < 1`
   - Bidirectional equivalences between Mathlib's `RiemannHypothesis`, `RiemannZetaZerosOnLine`,
     `RiemannZetaCriticalStripZerosOnLine`, and `RiemannZetaNonvanishingRightOfHalf`
3. **Euler-Factor Nonvanishing, `LSeries` Agreement & Exact GRH Equivalences**
   - Explicit Euler-factor nonvanishing `1 - χ(p) p^(-s) ≠ 0` on `Re(s) > 0`
   - `LFunction_changeLevel_eq_zero_iff_of_re_pos` and `LFunction_eq_zero_iff_primitive_of_re_pos`
   - `LFunction_eq_LSeries` agreement on `Re(s) > 1` and specialization `L(1, s) = ζ(s)`
   - Full bidirectional equivalence cycle:
     `ZeroFreeAll ↔ DirichletLNonvanishingRightOfHalf ↔ DirichletLZerosOnLine ↔ PrimitiveDirichletLZerosOnLine`
4. **Elementary Chebyshev, von Mangoldt, Cesàro-Ramp & Robin–Lagarias Bridges**
   - Exact `-ζ'/ζ` and `-L'/L` `LSeries` bridges for `Λ` and `χ · Λ` on `Re(s) > 1`
   - `chebyshevPsi`, `chebyshevRamp`, exact agreement with `RHDirect.ramp`, `RHDirect.Gz`, `RHDirect.Gchi`
   - Discrete Abel summation identity for `chebyshevRamp` in terms of `chebyshevPsi`
   - Chebyshev's factorial identity `∑_{n=1}^N log n = ∑_{d=1}^N Λ(d) ⌊N/d⌋`, two-sided sandwich,
     and unconditional linear bound `Gz N ≤ (1 + γ) N`
   - Robin & Lagarias inequalities: exact boundary values (`n = 1`, `σ(5040) = 19344`) and
     elementary proof that Robin's bound strictly implies Lagarias's bound for all `n ≥ 3`.
-/

noncomputable section

open Complex DirichletCharacter Filter Topology
open scoped ArithmeticFunction.vonMangoldt

namespace RHDirect

/-! ## 1. Analytic Conjugation & Zero Symmetries -/

/-- Schwarz reflection derivative: if `f` is complex-differentiable at `conj z`, then
`s ↦ conj (f (conj s))` is complex-differentiable at `z` with derivative `conj f'`. -/
lemma hasDerivAt_conj_conj {f : ℂ → ℂ} {f' z : ℂ}
    (hf : HasDerivAt f f' (starRingEnd ℂ z)) :
    HasDerivAt (fun s => starRingEnd ℂ (f (starRingEnd ℂ s))) (starRingEnd ℂ f') z := by
  rw [hasDerivAt_iff_isLittleO] at hf ⊢
  have hcomp := hf.comp_tendsto (Complex.continuous_conj.tendsto z)
  refine (Asymptotics.isLittleO_iff.mpr fun c hc => ?_)
  filter_upwards [Asymptotics.isLittleO_iff.mp hcomp hc] with x hx
  have h1 : starRingEnd ℂ (f (starRingEnd ℂ x)) - starRingEnd ℂ (f (starRingEnd ℂ z)) -
      (x - z) • starRingEnd ℂ f' =
      starRingEnd ℂ (f (starRingEnd ℂ x) - f (starRingEnd ℂ z) -
        (starRingEnd ℂ x - starRingEnd ℂ z) • f') := by
    simp [smul_eq_mul, map_sub, map_mul]
  have h2 : ‖starRingEnd ℂ x - starRingEnd ℂ z‖ = ‖x - z‖ := by
    rw [← map_sub, Complex.norm_conj]
  rw [h1, Complex.norm_conj, ← h2]
  simpa [Function.comp_apply] using hx

/-- Complex conjugation of a natural-number complex power `n ^ s`. -/
lemma natCast_cpow_conj (n : ℕ) (s : ℂ) :
    starRingEnd ℂ ((n : ℂ) ^ s) = (n : ℂ) ^ (starRingEnd ℂ s) := by
  by_cases hn : n = 0
  · subst hn
    by_cases hs : s = 0
    · subst hs; simp
    · have hs' : starRingEnd ℂ s ≠ 0 := by
        intro h; exact hs ((map_eq_zero (starRingEnd ℂ)).mp h)
      simp [Complex.zero_cpow hs, Complex.zero_cpow hs']
  · have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero hne,
      ← Complex.exp_conj, map_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_log hpos.le,
      Complex.conj_ofReal]

/-- Termwise conjugation of a Dirichlet character `LSeries` swaps `χ` and `χ⁻¹`. -/
theorem LSeries_conj {N : ℕ} (χ : DirichletCharacter ℂ N) (s : ℂ) :
    starRingEnd ℂ (LSeries (χ ·) s) = LSeries (χ⁻¹ ·) (starRingEnd ℂ s) := by
  unfold LSeries
  rw [← Complex.conjCLE_apply, Complex.conjCLE.map_tsum]
  congr 1
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn, ↓reduceIte, Complex.conjCLE_apply, map_div₀,
      natCast_cpow_conj]
    have hstar : starRingEnd ℂ (χ (n : ZMod N)) = χ⁻¹ (n : ZMod N) := by
      simpa [RCLike.star_def] using MulChar.star_apply' χ (n : ZMod N)
    rw [hstar]

private theorem LFunction_conj_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : s ≠ 1) :
    LFunction χ⁻¹ (starRingEnd ℂ s) = starRingEnd ℂ (LFunction χ s) := by
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) _).isPreconnected
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  have hhs : starRingEnd ℂ s ∈ ({1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    apply hs
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (f := fun z => LFunction χ⁻¹ z)
    (g := fun z => starRingEnd ℂ (LFunction χ (starRingEnd ℂ z)))
    ?_ ?_ hpc h2 ?_ hhs
  · simpa using hEq
  · refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    exact (differentiableAt_LFunction χ⁻¹ z (.inl hz)).differentiableWithinAt
  · refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    have hzc : starRingEnd ℂ z ≠ 1 := fun h => hz (by
      have := congrArg (starRingEnd ℂ) h; simpa using this)
    exact (hasDerivAt_conj_conj
      (differentiableAt_LFunction χ (starRingEnd ℂ z) (.inl hzc)).hasDerivAt).differentiableAt.differentiableWithinAt
  · refine eventually_of_mem
      ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : 1 < (2 : ℂ).re))
      (fun t (ht : 1 < t.re) => ?_)
    have htc : 1 < (starRingEnd ℂ t).re := by simpa using ht
    dsimp only
    rw [LFunction_eq_LSeries χ⁻¹ ht, LFunction_eq_LSeries χ htc, LSeries_conj]
    simp

/-- Conjugation symmetry of Dirichlet `L`-functions: `L(χ⁻¹, conj s) = conj (L(χ, s))`
whenever `χ ≠ 1` or `s ≠ 1`. -/
theorem LFunction_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (h : χ ≠ 1 ∨ s ≠ 1) :
    LFunction χ⁻¹ (starRingEnd ℂ s) = starRingEnd ℂ (LFunction χ s) := by
  rcases h with hχ | hs
  · have hχ' : χ⁻¹ ≠ 1 := by
      intro h1; exact hχ (by simpa using congrArg Inv.inv h1)
    have hcont1 : Continuous (fun z => LFunction χ⁻¹ (starRingEnd ℂ z)) :=
      (differentiable_LFunction hχ').continuous.comp Complex.continuous_conj
    have hcont2 : Continuous (fun z => starRingEnd ℂ (LFunction χ z)) :=
      Complex.continuous_conj.comp (differentiable_LFunction hχ).continuous
    exact congrFun (hcont1.ext_on (dense_compl_singleton 1) hcont2 fun z hz =>
      LFunction_conj_of_ne_one χ hz) s
  · exact LFunction_conj_of_ne_one χ hs

/-- Conjugation symmetry of the Riemann zeta function away from its pole at `s = 1`. -/
theorem riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
  have h := LFunction_conj (1 : DirichletCharacter ℂ 1) (.inr hs)
  rw [inv_one, LFunction_modOne_eq] at h
  exact h

/-- Complex conjugation preserves zeros of `ζ(s)` away from `s = 1`. -/
theorem riemannZeta_eq_zero_conj_iff {s : ℂ} (hs : s ≠ 1) :
    riemannZeta (starRingEnd ℂ s) = 0 ↔ riemannZeta s = 0 := by
  rw [riemannZeta_conj hs, map_eq_zero]

/-- Reflection `s ↦ 1 - s` preserves zeros of `ζ(s)` in the critical strip `0 < Re(s) < 1`. -/
theorem riemannZeta_eq_zero_one_sub_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta (1 - s) = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := fun e => by rw [e, zero_re] at h0; exact lt_irrefl _ h0
  have h1s0 : 1 - s ≠ 0 := fun e => by
    have := sub_eq_zero.mp e
    rw [← this, one_re] at h1
    exact lt_irrefl _ h1
  have h1s_pos : 0 < (1 - s).re := by rw [sub_re, one_re]; linarith
  have hGs : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  have hG1s : Gammaℝ (1 - s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos h1s_pos
  rw [riemannZeta_def_of_ne_zero h1s0, riemannZeta_def_of_ne_zero hs0,
    completedRiemannZeta_one_sub, div_eq_zero_iff, div_eq_zero_iff]
  simp [hGs, hG1s]

/-- Reflection across the critical line `Re(s) = 1/2` (`s ↦ 1 - conj s`, preserving `Im(s)`)
preserves zeros of `ζ(s)` in the critical strip `0 < Re(s) < 1`. -/
theorem riemannZeta_eq_zero_one_sub_conj_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta (1 - starRingEnd ℂ s) = 0 ↔ riemannZeta s = 0 := by
  have hs1 : s ≠ 1 := fun e => by rw [e, one_re] at h1; exact lt_irrefl _ h1
  have h0' : 0 < (starRingEnd ℂ s).re := by simpa using h0
  have h1' : (starRingEnd ℂ s).re < 1 := by simpa using h1
  rw [riemannZeta_eq_zero_one_sub_iff h0' h1', riemannZeta_eq_zero_conj_iff hs1]

/-- Four-fold symmetry of critical-strip zeros of `ζ(s)`: if `s` is a zero in `0 < Re(s) < 1`,
then `conj s`, `1 - s`, and `1 - conj s` are all critical-strip zeros as well. -/
theorem riemannZeta_fourfold_zero_symmetry {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) :
    riemannZeta (starRingEnd ℂ s) = 0 ∧
    riemannZeta (1 - s) = 0 ∧
    riemannZeta (1 - starRingEnd ℂ s) = 0 := by
  have hs1 : s ≠ 1 := fun e => by rw [e, one_re] at h1; exact lt_irrefl _ h1
  exact ⟨(riemannZeta_eq_zero_conj_iff hs1).mpr hz,
    (riemannZeta_eq_zero_one_sub_iff h0 h1).mpr hz,
    (riemannZeta_eq_zero_one_sub_conj_iff h0 h1).mpr hz⟩

/-- Complex conjugation pairs zeros of `L(χ, s)` with zeros of `L(χ⁻¹, conj s)`. -/
theorem LFunction_eq_zero_conj_iff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (h : χ ≠ 1 ∨ s ≠ 1) :
    LFunction χ⁻¹ (starRingEnd ℂ s) = 0 ↔ LFunction χ s = 0 := by
  rw [LFunction_conj χ h, map_eq_zero]

private lemma gammaFactor_ne_zero_of_re_pos {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (h0 : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos h0
  · rw [ho.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos (by rw [add_re, one_re]; linarith)

private lemma LFunction_eq_zero_one_sub_of_isPrimitive {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : LFunction χ s = 0) :
    LFunction χ⁻¹ (1 - s) = 0 := by
  have hs0 : s ≠ 0 := fun e => by rw [e, zero_re] at h0; exact lt_irrefl _ h0
  have h1s0 : 1 - s ≠ 0 := fun e => by
    have := sub_eq_zero.mp e
    rw [← this, one_re] at h1
    exact lt_irrefl _ h1
  have hc : completedLFunction χ s = 0 := by
    rw [LFunction_eq_completed_div_gammaFactor χ s (.inl hs0), div_eq_zero_iff] at hz
    exact hz.resolve_right (gammaFactor_ne_zero_of_re_pos χ h0)
  have hχinv : χ⁻¹.IsPrimitive := by
    rw [isPrimitive_def, conductor_inv]; exact hχ
  have hfe := hχinv.completedLFunction_one_sub s
  rw [inv_inv, hc, mul_zero] at hfe
  rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (.inl h1s0), hfe, zero_div]

/-- Functional-equation reflection `s ↦ 1 - s` pairs critical-strip zeros of primitive `L(χ, s)`
with critical-strip zeros of `L(χ⁻¹, 1 - s)`. -/
theorem LFunction_eq_zero_one_sub_iff_of_isPrimitive {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    LFunction χ⁻¹ (1 - s) = 0 ↔ LFunction χ s = 0 := by
  constructor
  · intro hz
    have hχinv : χ⁻¹.IsPrimitive := by
      rw [isPrimitive_def, conductor_inv]; exact hχ
    have h0' : 0 < (1 - s).re := by rw [sub_re, one_re]; linarith
    have h1' : (1 - s).re < 1 := by rw [sub_re, one_re]; linarith
    have hback := LFunction_eq_zero_one_sub_of_isPrimitive hχinv h0' h1' hz
    simpa [inv_inv] using hback
  · exact LFunction_eq_zero_one_sub_of_isPrimitive hχ h0 h1

/-- Reflection across `Re(s) = 1/2` (`s ↦ 1 - conj s`) preserves the critical-strip zeros of
the *same* primitive Dirichlet `L`-function `L(χ, s)`. -/
theorem LFunction_eq_zero_one_sub_conj_iff_of_isPrimitive {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    LFunction χ (1 - starRingEnd ℂ s) = 0 ↔ LFunction χ s = 0 := by
  have hs1 : s ≠ 1 := fun e => by rw [e, one_re] at h1; exact lt_irrefl _ h1
  have hχinv : χ⁻¹.IsPrimitive := by
    rw [isPrimitive_def, conductor_inv]; exact hχ
  have h0' : 0 < (starRingEnd ℂ s).re := by simpa using h0
  have h1' : (starRingEnd ℂ s).re < 1 := by simpa using h1
  have hstep := LFunction_eq_zero_one_sub_iff_of_isPrimitive hχinv h0' h1'
  rw [inv_inv] at hstep
  rw [hstep, LFunction_eq_zero_conj_iff χ (.inr hs1)]

/-! ## 2. Trivial-Zero Characterization & Exact RH Equivalences -/

/-- Critical-strip formulation of the Riemann Hypothesis. -/
def RiemannZetaCriticalStripZerosOnLine : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2

/-- Right-half-plane nonvanishing formulation of the Riemann Hypothesis. -/
def RiemannZetaNonvanishingRightOfHalf : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0

/-- Trivial zeros of `ζ(s)` at the negative even integers `-2, -4, -6, ...`. -/
theorem riemannZeta_eq_zero_of_neg_two_mul_succ (n : ℕ) :
    riemannZeta (-2 * ((n : ℂ) + 1)) = 0 :=
  riemannZeta_neg_two_mul_nat_add_one n

/-- Exact characterization of all zeros of `ζ(s)` in the closed left half-plane `Re(s) ≤ 0`:
they are precisely the negative even integers `-2 * (n + 1)`. -/
theorem riemannZeta_eq_zero_of_re_nonpos_iff {s : ℂ} (hs : s.re ≤ 0) :
    riemannZeta s = 0 ↔ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
  constructor
  · intro hz
    have hs0 : s ≠ 0 := fun e => by
      rw [e, riemannZeta_zero] at hz
      norm_num at hz
    by_contra htriv
    have hG : Gammaℝ s ≠ 0 := fun hg => by
      obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hg
      rcases n with _ | n
      · rw [Nat.cast_zero, mul_zero, neg_zero] at hn; exact hs0 hn
      · exact htriv ⟨n, by rw [hn, Nat.cast_add_one, neg_mul]⟩
    have hc : completedRiemannZeta s = 0 := by
      rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hz
      exact hz.resolve_right hG
    have h1s : 1 - s ≠ 0 := fun e => by
      have hr := congrArg Complex.re e
      rw [sub_re, one_re, zero_re] at hr
      linarith
    have hz' : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_def_of_ne_zero h1s, completedRiemannZeta_one_sub, hc, zero_div]
    have hge1 : 1 ≤ (1 - s).re := by rw [sub_re, one_re]; linarith
    exact riemannZeta_ne_zero_of_one_le_re hge1 hz'
  · rintro ⟨n, rfl⟩
    exact riemannZeta_eq_zero_of_neg_two_mul_succ n

/-- `ζ(s)` has no nontrivial zeros in `Re(s) ≤ 0`. -/
theorem riemannZeta_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0)
    (htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) : riemannZeta s ≠ 0 :=
  fun hz => htriv ((riemannZeta_eq_zero_of_re_nonpos_iff hs).mp hz)

/-- Every nontrivial zero of `ζ(s)` lies strictly inside the critical strip `0 < Re(s) < 1`. -/
theorem riemannZeta_nontrivial_zero_mem_strip {s : ℂ}
    (hz : riemannZeta s = 0) (htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hle
    exact riemannZeta_ne_zero_of_re_nonpos (not_lt.mp hle) htriv hz
  · by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hz

/-- Mathlib's `RiemannHypothesis` and `RiemannZetaZerosOnLine` are definitionally identical. -/
theorem riemannHypothesis_iff_riemannZetaZerosOnLine :
    RiemannHypothesis ↔ RiemannZetaZerosOnLine := Iff.rfl

/-- Exact equivalence between `RiemannHypothesis` and the critical-strip zero-line statement. -/
theorem riemannHypothesis_iff_criticalStrip :
    RiemannHypothesis ↔ RiemannZetaCriticalStripZerosOnLine := by
  constructor
  · intro hRH s h0 h1 hz
    have htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, rfl⟩
      have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hs1 : s ≠ 1 := fun e => by rw [e, one_re] at h1; exact lt_irrefl _ h1
    exact hRH s hz htriv hs1
  · intro hStrip s hz htriv _
    obtain ⟨h0, h1⟩ := riemannZeta_nontrivial_zero_mem_strip hz htriv
    exact hStrip s h0 h1 hz

/-- Exact equivalence between `RiemannHypothesis` and nonvanishing of `ζ(s)` on `Re(s) > 1/2`. -/
theorem riemannHypothesis_iff_nonvanishingRightOfHalf :
    RiemannHypothesis ↔ RiemannZetaNonvanishingRightOfHalf := by
  rw [riemannHypothesis_iff_criticalStrip]
  constructor
  · intro hStrip s hre _ hz
    rcases lt_or_ge s.re 1 with h1 | hge1
    · have h0 : 0 < s.re := by linarith
      have heq := hStrip s h0 h1 hz
      linarith
    · exact riemannZeta_ne_zero_of_one_le_re hge1 hz
  · intro hRight s h0 h1 hz
    have hs1 : s ≠ 1 := fun e => by rw [e, one_re] at h1; exact lt_irrefl _ h1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hre : 1 / 2 < (1 - s).re := by rw [sub_re, one_re]; linarith
      have h1s1 : 1 - s ≠ 1 := fun e => by
        have hs0 : s = 0 := sub_eq_self.mp e
        rw [hs0, zero_re] at h0
        exact lt_irrefl _ h0
      exact hRight (1 - s) hre h1s1 ((riemannZeta_eq_zero_one_sub_iff h0 h1).mpr hz)
    · exact hRight s hgt hs1 hz

/-- Exact equivalence between `RiemannZetaZerosOnLine` and `RiemannZetaNonvanishingRightOfHalf`. -/
theorem riemannZetaZerosOnLine_iff_nonvanishingRightOfHalf :
    RiemannZetaZerosOnLine ↔ RiemannZetaNonvanishingRightOfHalf :=
  riemannHypothesis_iff_riemannZetaZerosOnLine.symm.trans
    riemannHypothesis_iff_nonvanishingRightOfHalf

/-- Symmetry corollary: `RiemannHypothesis` is also equivalent to zero-freeness in `0 < Re(s) < 1/2`. -/
theorem riemannHypothesis_iff_no_zeros_leftOfHalf :
    RiemannHypothesis ↔ ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → riemannZeta s ≠ 0 := by
  rw [riemannHypothesis_iff_nonvanishingRightOfHalf]
  constructor
  · intro hRight s h0 hlt hz
    have h1 : s.re < 1 := by linarith
    have hre : 1 / 2 < (1 - s).re := by rw [sub_re, one_re]; linarith
    have h1s1 : 1 - s ≠ 1 := fun e => by
      have hs0 : s = 0 := sub_eq_self.mp e
      rw [hs0, zero_re] at h0
      exact lt_irrefl _ h0
    exact hRight (1 - s) hre h1s1 ((riemannZeta_eq_zero_one_sub_iff h0 h1).mpr hz)
  · intro hLeft s hre _ hz
    rcases lt_or_ge s.re 1 with h1 | hge1
    · have h0 : 0 < s.re := by linarith
      have h0' : 0 < (1 - s).re := by rw [sub_re, one_re]; linarith
      have hlt' : (1 - s).re < 1 / 2 := by rw [sub_re, one_re]; linarith
      exact hLeft (1 - s) h0' hlt' ((riemannZeta_eq_zero_one_sub_iff h0 h1).mpr hz)
    · exact riemannZeta_ne_zero_of_one_le_re hge1 hz

/-! ## 3. Euler-Factor Nonvanishing, `LSeries` Agreement & Exact GRH Equivalences -/

/-- Explicit local Euler-factor nonvanishing on `Re(s) > 0`: for any prime `p` and character `χ`,
`1 - χ(p) p^(-s) ≠ 0` because `‖χ(p) p^(-s)‖ ≤ p^(-Re s) < 1`. -/
theorem eulerFactor_ne_zero_of_re_pos {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {p : ℕ} (hp : p.Prime) {s : ℂ} (h0 : 0 < s.re) :
    1 - χ p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro hpe
  have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_natCast_cpow_of_pos hp.pos, neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (Nat.one_lt_cast.2 hp.one_lt) (neg_lt_zero.2 h0)
  have hn : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)) hpow
  rw [(sub_eq_zero.1 hpe).symm, norm_one] at hn
  exact lt_irrefl _ hn

/-- Product of imprimitive Euler factors over `N.primeFactors` never vanishes on `Re(s) > 0`. -/
theorem eulerFactorProd_ne_zero_of_re_pos {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) {s : ℂ} (h0 : 0 < s.re) :
    ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s)) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hp =>
    eulerFactor_ne_zero_of_re_pos χ (Nat.prime_of_mem_primeFactors hp) h0

/-- Changing level preserves exact zero locations on `Re(s) > 0`. -/
theorem LFunction_changeLevel_eq_zero_iff_of_re_pos {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) {s : ℂ}
    (h0 : 0 < s.re) (h : χ ≠ 1 ∨ s ≠ 1) :
    LFunction (changeLevel hMN χ) s = 0 ↔ LFunction χ s = 0 := by
  rw [LFunction_changeLevel hMN χ h, mul_eq_zero]
  simp [eulerFactorProd_ne_zero_of_re_pos (N := N) χ h0]

/-- On `Re(s) > 0`, an imprimitive Dirichlet `L`-function vanishes at `s` iff its underlying
primitive `L`-function vanishes at `s`. -/
theorem LFunction_eq_zero_iff_primitive_of_re_pos {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (h0 : 0 < s.re) (h : χ ≠ 1 ∨ s ≠ 1) :
    LFunction χ s = 0 ↔
      @LFunction χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter s = 0 := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hcond : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
    rcases h with hχ | hs1
    · left
      intro h1
      apply hχ
      rw [← χ.changeLevel_primitiveCharacter, h1, map_one]
    · exact .inr hs1
  have hiff := LFunction_changeLevel_eq_zero_iff_of_re_pos
    χ.conductor_dvd_level χ.primitiveCharacter h0 hcond
  simpa [χ.changeLevel_primitiveCharacter] using hiff

/-- Statement sanity check: `LFunction χ s` agrees with the convergent Dirichlet series
`LSeries (χ ·) s` throughout the half-plane `Re(s) > 1`. -/
theorem LFunction_eq_LSeries_of_one_lt_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) : LFunction χ s = LSeries (χ ·) s :=
  LFunction_eq_LSeries χ hs

/-- Statement sanity check: `L(1_1, s) = ζ(s)` everywhere, and `ζ(s) = LSeries 1 s` on `Re(s) > 1`. -/
theorem LFunction_modOne_eq_riemannZeta (s : ℂ) :
    LFunction (1 : DirichletCharacter ℂ 1) s = riemannZeta s :=
  congrFun LFunction_modOne_eq s

theorem riemannZeta_eq_LSeries_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = LSeries 1 s :=
  (LSeries_one_eq_riemannZeta hs).symm

/-- On `Re(s) > 0` with `s ≠ 1`, the trivial character `L`-function mod `N` has the exact same
zeros as `ζ(s)`. -/
theorem LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos (N : ℕ) [NeZero N]
    {s : ℂ} (h0 : 0 < s.re) (hs1 : s ≠ 1) :
    LFunction (1 : DirichletCharacter ℂ N) s = 0 ↔ riemannZeta s = 0 := by
  have h := LFunction_changeLevel_eq_zero_iff_of_re_pos N.one_dvd (1 : DirichletCharacter ℂ 1)
    h0 (.inr hs1)
  rwa [map_one, LFunction_modOne_eq] at h

/-- Exact bidirectional equivalence: `DirichletLNonvanishingRightOfHalf ↔ DirichletLZerosOnLine`. -/
theorem dirichletLNonvanishingRightOfHalf_iff_dirichletLZerosOnLine :
    DirichletLNonvanishingRightOfHalf ↔ DirichletLZerosOnLine := by
  constructor
  · intro hRight N _ χ s h0 h1 hz
    have hs1 : s ≠ 1 := fun e => by rw [e, one_re] at h1; exact lt_irrefl _ h1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
      have hL : LFunction χ.primitiveCharacter s = 0 :=
        (LFunction_eq_zero_iff_primitive_of_re_pos χ h0 (.inr hs1)).mp hz
      have hL' : LFunction χ.primitiveCharacter⁻¹ (1 - s) = 0 :=
        (LFunction_eq_zero_one_sub_iff_of_isPrimitive χ.primitiveCharacter_isPrimitive h0 h1).mpr hL
      have hre : 1 / 2 < (1 - s).re := by rw [sub_re, one_re]; linarith
      have h1s1 : 1 - s ≠ 1 := fun e => by
        have hs0 : s = 0 := sub_eq_self.mp e
        rw [hs0, zero_re] at h0
        exact lt_irrefl _ h0
      exact hRight χ.conductor χ.primitiveCharacter⁻¹ (1 - s) hre (.inr h1s1) hL'
    · exact hRight N χ s hgt (.inr hs1) hz
  · intro hLine N _ χ s hre hs hz
    rcases lt_or_ge s.re 1 with h1 | hge1
    · have h0 : 0 < s.re := by linarith
      have heq := hLine N χ s h0 h1 hz
      linarith
    · exact LFunction_ne_zero_of_one_le_re χ hs hge1 hz

/-- Exact bidirectional equivalence: `DirichletLZerosOnLine ↔ PrimitiveDirichletLZerosOnLine`. -/
theorem dirichletLZerosOnLine_iff_primitiveDirichletLZerosOnLine :
    DirichletLZerosOnLine ↔ PrimitiveDirichletLZerosOnLine := by
  constructor
  · intro hAll N _ χ _ s h0 h1 hz
    exact hAll N χ s h0 h1 hz
  · intro hPrim N _ χ s h0 h1 hz
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hs1 : s ≠ 1 := fun e => by rw [e, one_re] at h1; exact lt_irrefl _ h1
    have hL : LFunction χ.primitiveCharacter s = 0 :=
      (LFunction_eq_zero_iff_primitive_of_re_pos χ h0 (.inr hs1)).mp hz
    exact hPrim χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive s h0 h1 hL

/-- Exact bidirectional equivalence:
`DirichletLNonvanishingRightOfHalf ↔ PrimitiveDirichletLZerosOnLine`. -/
theorem dirichletLNonvanishingRightOfHalf_iff_primitiveDirichletLZerosOnLine :
    DirichletLNonvanishingRightOfHalf ↔ PrimitiveDirichletLZerosOnLine :=
  dirichletLNonvanishingRightOfHalf_iff_dirichletLZerosOnLine.trans
    dirichletLZerosOnLine_iff_primitiveDirichletLZerosOnLine

/-- Exact bidirectional equivalence with the `RHDirect.Interfaces` core predicate `ZeroFreeAll`. -/
theorem zeroFreeAll_iff_dirichletLNonvanishingRightOfHalf :
    ZeroFreeAll ↔ DirichletLNonvanishingRightOfHalf := by
  constructor
  · intro hZ N _ χ s hre hs hz
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have h0 : 0 < s.re := by linarith
    have hL : LFunction χ.primitiveCharacter s = 0 :=
      (LFunction_eq_zero_iff_primitive_of_re_pos χ h0 hs).mp hz
    exact hZ (PChar.of χ) s hre hL
  · intro hRight ψ s hre
    by_cases hs : ψ.χ ≠ 1 ∨ s ≠ 1
    · exact hRight ψ.N ψ.χ s hre hs
    · obtain ⟨hχ1, hs1⟩ := not_or.mp hs
      have hχ1 : ψ.χ = 1 := not_not.mp hχ1
      have hs1 : s = 1 := not_not.mp hs1
      subst hs1
      have hN1 : ψ.N = 1 := by
        have hcond := ψ.prim
        rw [isPrimitive_def, hχ1, conductor_one] at hcond
        exact hcond.symm
      cases ψ with
      | mk N χ prim =>
        dsimp only at hχ1 hN1 ⊢
        subst hN1
        rw [LFunction_modOne_eq]
        exact riemannZeta_ne_zero_of_one_le_re (by simp)

/-- GRH (`DirichletLZerosOnLine`) directly implies `RiemannHypothesis`. -/
theorem riemannHypothesis_of_dirichletLZerosOnLine (hGRH : DirichletLZerosOnLine) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_criticalStrip]
  intro s h0 h1 hz
  exact hGRH 1 1 s h0 h1 (by rwa [LFunction_modOne_eq])

/-! ## 4. Elementary Chebyshev, von Mangoldt, Cesàro-Ramp & Robin–Lagarias Bridges -/

/-- Exact `LSeries` logarithmic-derivative bridge for `ζ(s)` on `Re(s) > 1`:
`∑ Λ(n) n^(-s) = -ζ'(s) / ζ(s)`. -/
theorem LSeries_vonMangoldt_eq_neg_deriv_zeta_div {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (Λ n : ℂ)) s = -deriv riemannZeta s / riemannZeta s := by
  simpa using ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/-- Exact `LSeries` logarithmic-derivative bridge for `L(χ, s)` on `Re(s) > 1`:
`∑ χ(n) Λ(n) n^(-s) = -L'(χ, s) / L(χ, s)`. -/
theorem LSeries_twist_vonMangoldt_eq_neg_deriv_LFunction_div {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => χ n * (Λ n : ℂ)) s =
      -deriv (LFunction χ) s / LFunction χ s := by
  rw [LFunction_eq_LSeries χ hs, deriv_LFunction_eq_deriv_LSeries χ hs]
  exact LSeries_twist_vonMangoldt_eq χ hs

/-- Classical Chebyshev summatory function `ψ(x) = ∑_{n ≤ x} Λ(n)`. -/
def chebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n

/-- Real Cesàro-1 / Riesz ramp sum `∑_{n ≤ y} Λ(n) (y/n - 1)_+`. -/
def chebyshevRamp (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊y⌋₊ + 1), Λ n * max (y / (n : ℝ) - 1) 0

theorem chebyshevPsi_nonneg (x : ℝ) : 0 ≤ chebyshevPsi x :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

theorem chebyshevPsi_mono {x y : ℝ} (hxy : x ≤ y) : chebyshevPsi x ≤ chebyshevPsi y := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.add_le_add_right (Nat.floor_mono hxy) 1)
  · intro _ _ _; exact ArithmeticFunction.vonMangoldt_nonneg

theorem chebyshevPsi_zero : chebyshevPsi 0 = 0 := by
  simp [chebyshevPsi]

theorem chebyshevPsi_one : chebyshevPsi 1 = 0 := by
  simp [chebyshevPsi, Finset.sum_range_succ, ArithmeticFunction.vonMangoldt_apply_one]

theorem chebyshevRamp_nonneg (y : ℝ) : 0 ≤ chebyshevRamp y :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_max_right _ _)

/-- `RHDirect.ramp (fun _ => 1) y` is purely real and coincides with `chebyshevRamp y`. -/
theorem ramp_const_one_eq_ofReal (y : ℝ) :
    ramp (fun _ => 1) y = (chebyshevRamp y : ℂ) := by
  simp only [ramp, chebyshevRamp, mul_one, Complex.ofReal_sum, Complex.ofReal_mul]

/-- Exact bridge between `RHDirect.Gz` and `chebyshevRamp`. -/
theorem Gz_eq_chebyshevRamp (y : ℝ) :
    Gz y = chebyshevRamp y - y * Real.log y + (1 + Real.eulerMascheroniConstant) * y := by
  rw [Gz, ramp_const_one_eq_ofReal, Complex.ofReal_re]

/-- Sanity check: `RHDirect.Gchi` for the trivial character mod `1` has real part `RHDirect.Gz`. -/
theorem Gchi_modOne_re (y : ℝ) :
    (Gchi (1 : DirichletCharacter ℂ 1) y).re = Gz y := by
  simp only [Gchi, ↓reduceIte, Gz]
  have hramp : ramp (fun n : ℕ => ((1 : DirichletCharacter ℂ 1) n)) y = ramp (fun _ => 1) y := by
    simp only [ramp]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h1 : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 :=
      MulChar.one_apply (isUnit_of_subsingleton _)
    rw [h1]
  rw [hramp]
  simp

private lemma sum_range_succ_eq_sum_Icc (f : ℕ → ℝ) (hf0 : f 0 = 0) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), f n = ∑ n ∈ Finset.Icc 1 N, f n := by
  have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have h0 : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
  rw [hset, Finset.sum_insert h0, hf0, zero_add]

/-- For `y ≥ 1`, `chebyshevRamp y` simplifies to a sum over `1 ≤ n ≤ ⌊y⌋₊` without `max`. -/
theorem chebyshevRamp_eq_sum_Icc {y : ℝ} (hy : 1 ≤ y) :
    chebyshevRamp y = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n * (y / (n : ℝ) - 1) := by
  unfold chebyshevRamp
  rw [sum_range_succ_eq_sum_Icc _ (by simp)]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn.1
  have hn_le : (n : ℝ) ≤ y := le_trans (Nat.cast_le.mpr hn.2) (Nat.floor_le (by linarith))
  have hge : 0 ≤ y / (n : ℝ) - 1 := by
    rw [sub_nonneg, one_le_div hn_pos]
    exact hn_le
  rw [max_eq_left hge]

/-- Decomposition `chebyshevRamp y = y * ∑_{1 ≤ n ≤ y} Λ(n)/n - ψ(y)`. -/
theorem chebyshevRamp_eq_sub_chebyshevPsi {y : ℝ} (hy : 1 ≤ y) :
    chebyshevRamp y = y * (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n / (n : ℝ)) - chebyshevPsi y := by
  rw [chebyshevRamp_eq_sum_Icc hy]
  have hpsi : chebyshevPsi y = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n := by
    unfold chebyshevPsi
    exact sum_range_succ_eq_sum_Icc _ (by simp) _
  rw [hpsi, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

private lemma abel_sum_Icc (a : ℕ → ℝ) (f : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, a n * f n =
      (∑ k ∈ Finset.Ico 1 N, (∑ n ∈ Finset.Icc 1 k, a n) * (f k - f (k + 1))) +
        (∑ n ∈ Finset.Icc 1 N, a n) * f N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hIco : Finset.Ico 1 (m + 1) = insert m (Finset.Ico 1 m) := by
      ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hm_not_Icc : m + 1 ∉ Finset.Icc 1 m := by simp
    have hm_not_Ico : m ∉ Finset.Ico 1 m := by simp
    rw [hIcc, Finset.sum_insert hm_not_Icc, ih, hIco, Finset.sum_insert hm_not_Ico,
      Finset.sum_insert hm_not_Icc]
    ring

/-- Exact discrete Abel summation identity bridging `chebyshevRamp y` directly to `chebyshevPsi k`. -/
theorem chebyshevRamp_eq_abel_sum {y : ℝ} (hy : 1 ≤ y) :
    chebyshevRamp y =
      (∑ k ∈ Finset.Ico 1 ⌊y⌋₊,
        chebyshevPsi (k : ℝ) * (y / (k : ℝ) - y / ((k + 1 : ℕ) : ℝ))) +
      chebyshevPsi (⌊y⌋₊ : ℝ) * (y / (⌊y⌋₊ : ℝ) - 1) := by
  have hN : 1 ≤ ⌊y⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hy)
  rw [chebyshevRamp_eq_sum_Icc hy]
  have habel := abel_sum_Icc (fun n => Λ n) (fun n => y / (n : ℝ) - 1) ⌊y⌋₊ hN
  rw [habel]
  have hpsi : ∀ m : ℕ, (∑ n ∈ Finset.Icc 1 m, Λ n) = chebyshevPsi (m : ℝ) := by
    intro m
    unfold chebyshevPsi
    rw [Nat.floor_natCast]
    exact (sum_range_succ_eq_sum_Icc _ (by simp) m).symm
  rw [hpsi ⌊y⌋₊]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hpsi k]
  ring

/-- Chebyshev's fundamental factorial identity:
`∑_{n=1}^N log n = ∑_{d=1}^N Λ(d) ⌊N/d⌋`. -/
theorem chebyshev_factorial_identity (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) =
      ∑ d ∈ Finset.Icc 1 N, Λ d * ((N / d : ℕ) : ℝ) := by
  have h1 : ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) =
      ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, Λ d := by
    refine Finset.sum_congr rfl fun n _ => ?_
    exact ArithmeticFunction.vonMangoldt_sum.symm
  rw [h1]
  have hswap :
      ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, Λ d =
        ∑ d ∈ Finset.Icc 1 N, ∑ _n ∈ (Finset.Icc 1 N).filter (d ∣ ·), Λ d := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdn, _⟩
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn.1
      have hdle : d ≤ n := Nat.le_of_dvd hn.1 hdn
      exact ⟨⟨hdpos, le_trans hdle hn.2⟩, hdn⟩
    · rintro ⟨_, hdn⟩
      exact ⟨hdn, Nat.ne_of_gt hn.1⟩
  rw [hswap]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  have hcard : ((Finset.Icc 1 N).filter (d ∣ ·)).card = N / d := by
    have hbij : ((Finset.Icc 1 N).filter (d ∣ ·)) = (Finset.Icc 1 (N / d)).image (d * ·) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hn1, hnN⟩, k, rfl⟩
        refine ⟨k, ⟨?_, ?_⟩, rfl⟩
        · by_contra hk
          have hk0 : k = 0 := by omega
          subst hk0; simp at hn1
        · exact (Nat.le_div_iff_mul_le hd.1).mpr (by rw [mul_comm]; exact hnN)
      · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
        refine ⟨⟨?_, ?_⟩, k, rfl⟩
        · exact Nat.mul_pos hd.1 hk1
        · have := (Nat.le_div_iff_mul_le hd.1).mp hkN
          rwa [mul_comm]
    rw [hbij, Finset.card_image_of_injective _ (mul_right_injective₀ (Nat.ne_of_gt hd.1)),
      Nat.card_Icc, Nat.add_sub_cancel]
  exact_mod_cast hcard

/-- Lower sandwich: `chebyshevRamp N ≤ ∑_{n=1}^N log n`. -/
theorem chebyshevRamp_le_sum_log {N : ℕ} (hN : 1 ≤ N) :
    chebyshevRamp (N : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) := by
  rw [chebyshevRamp_eq_sum_Icc (Nat.one_le_cast.mpr hN), Nat.floor_natCast,
    chebyshev_factorial_identity N]
  refine Finset.sum_le_sum fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd.1
  have hmod : N < d * (N / d + 1) := by
    have := Nat.div_add_mod N d
    have := Nat.mod_lt N hd.1
    linarith
  have hmodR : (N : ℝ) < (d : ℝ) * (((N / d : ℕ) : ℝ) + 1) := by exact_mod_cast hmod
  have hdiv : (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 :=
    (div_lt_iff₀ hd_pos).mpr (by linarith)
  linarith

/-- Upper sandwich: `∑_{n=1}^N log n ≤ chebyshevRamp N + chebyshevPsi N`. -/
theorem sum_log_le_chebyshevRamp_add_chebyshevPsi {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) ≤ chebyshevRamp (N : ℝ) + chebyshevPsi (N : ℝ) := by
  rw [chebyshevRamp_eq_sub_chebyshevPsi (Nat.one_le_cast.mpr hN), Nat.floor_natCast,
    sub_add_cancel, Finset.mul_sum, chebyshev_factorial_identity N]
  refine Finset.sum_le_sum fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd.1
  have hmul : d * (N / d) ≤ N := Nat.mul_div_le N d
  have hdiv : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hd_pos]
    have : (d : ℝ) * ((N / d : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmul
    linarith
  have hle : Λ d * ((N / d : ℕ) : ℝ) ≤ Λ d * ((N : ℝ) / (d : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv (ArithmeticFunction.vonMangoldt_nonneg (n := d))
  calc
    Λ d * ((N / d : ℕ) : ℝ) ≤ Λ d * ((N : ℝ) / (d : ℝ)) := hle
    _ = (N : ℝ) * (Λ d / (d : ℝ)) := by ring

/-- Unconditional elementary upper bound on `RHDirect.Gz` at natural arguments:
`Gz N ≤ (1 + γ) N` for all `N ≥ 1`. -/
theorem Gz_nat_le_linear {N : ℕ} (hN : 1 ≤ N) :
    Gz (N : ℝ) ≤ (1 + Real.eulerMascheroniConstant) * (N : ℝ) := by
  rw [Gz_eq_chebyshevRamp]
  have h1 : chebyshevRamp (N : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) :=
    chebyshevRamp_le_sum_log hN
  have h2 : ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) ≤ (N : ℝ) * Real.log (N : ℝ) := by
    calc
      ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ)
          ≤ ∑ _n ∈ Finset.Icc 1 N, Real.log (N : ℝ) := by
            refine Finset.sum_le_sum fun n hn => ?_
            rw [Finset.mem_Icc] at hn
            exact Real.log_le_log (Nat.cast_pos.mpr hn.1) (Nat.cast_le.mpr hn.2)
      _ = (N : ℝ) * Real.log (N : ℝ) := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  linarith

/-- Trivial elementary upper bound `ψ(x) ≤ ⌊x⌋₊ log x` for `x ≥ 1`. -/
theorem chebyshevPsi_le_floor_mul_log {x : ℝ} (hx : 1 ≤ x) :
    chebyshevPsi x ≤ (⌊x⌋₊ : ℝ) * Real.log x := by
  unfold chebyshevPsi
  rw [sum_range_succ_eq_sum_Icc _ (by simp)]
  calc
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n
        ≤ ∑ _n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log x := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [Finset.mem_Icc] at hn
          refine le_trans ArithmeticFunction.vonMangoldt_le_log ?_
          exact Real.log_le_log (Nat.cast_pos.mpr hn.1)
            (le_trans (Nat.cast_le.mpr hn.2) (Nat.floor_le (by linarith)))
    _ = (⌊x⌋₊ : ℝ) * Real.log x := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

/-- Robin's elementary criterion (1984): `σ(n) < e^γ n log(log n)` for all `n > 5040`. -/
def RobinInequality : Prop :=
  ∀ n : ℕ, 5040 < n →
    (ArithmeticFunction.sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ))

/-- Lagarias's elementary harmonic criterion (2002):
`σ(n) ≤ H_n + exp(H_n) log(H_n)` for all `n ≥ 1`. -/
def LagariasInequality : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (ArithmeticFunction.sigma 1 n : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)

/-- Exact equality holds in Lagarias's inequality at `n = 1` (`σ(1) = H_1 + e^{H_1} log H_1 = 1`). -/
theorem lagarias_eq_at_one :
    (ArithmeticFunction.sigma 1 1 : ℝ) =
      (harmonic 1 : ℝ) + Real.exp (harmonic 1 : ℝ) * Real.log (harmonic 1 : ℝ) := by
  simp [harmonic]

/-- Exact divisor sum at Robin's famous last counterexample `n = 5040`: `σ(5040) = 19344`,
computed directly via multiplicativity `5040 = 2^4 · 3^2 · 5 · 7`. -/
theorem sigma_5040 : ArithmeticFunction.sigma 1 5040 = 19344 := by
  have hm := ArithmeticFunction.isMultiplicative_sigma (k := 1)
  have h5040 : (5040 : ℕ) = 16 * (9 * (5 * 7)) := by norm_num
  rw [h5040,
    hm.map_mul_of_coprime (by decide : Nat.Coprime 16 (9 * (5 * 7))),
    hm.map_mul_of_coprime (by decide : Nat.Coprime 9 (5 * 7)),
    hm.map_mul_of_coprime (by decide : Nat.Coprime 5 7)]
  have h16 : ArithmeticFunction.sigma 1 16 = 31 := by decide
  have h9 : ArithmeticFunction.sigma 1 9 = 13 := by decide
  have h5 : ArithmeticFunction.sigma 1 5 = 6 := by decide
  have h7 : ArithmeticFunction.sigma 1 7 = 8 := by decide
  rw [h16, h9, h5, h7]
  norm_num

/-- Elementary Euler–Mascheroni comparison: for every `n ≥ 3`, Robin's upper bound
`e^γ n log(log n)` is strictly smaller than Lagarias's upper bound `H_n + exp(H_n) log(H_n)`. -/
theorem robin_bound_lt_lagarias_bound {n : ℕ} (hn : 3 ≤ n) :
    Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) <
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hγ_pos : 0 < Real.eulerMascheroniConstant :=
    lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant
  have hγ_lt : Real.eulerMascheroniConstant < (harmonic n : ℝ) - Real.log (n : ℝ) := by
    have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
    simpa [Real.eulerMascheroniSeq', hn0] using h
  have hlog_add_lt : Real.eulerMascheroniConstant + Real.log (n : ℝ) < (harmonic n : ℝ) := by
    linarith
  have hlog_lt_H : Real.log (n : ℝ) < (harmonic n : ℝ) := by linarith
  have hone_lt_log : (1 : ℝ) < Real.log (n : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hn_pos]
    have hexp : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    exact lt_of_lt_of_le hexp hn3
  have hloglog_pos : 0 < Real.log (Real.log (n : ℝ)) :=
    Real.log_pos hone_lt_log
  have hloglog_lt : Real.log (Real.log (n : ℝ)) < Real.log (harmonic n : ℝ) :=
    Real.log_lt_log (by linarith) hlog_lt_H
  have hexp_lt : Real.exp Real.eulerMascheroniConstant * (n : ℝ) < Real.exp (harmonic n : ℝ) := by
    calc
      Real.exp Real.eulerMascheroniConstant * (n : ℝ)
          = Real.exp Real.eulerMascheroniConstant * Real.exp (Real.log (n : ℝ)) := by
            rw [Real.exp_log hn_pos]
      _ = Real.exp (Real.eulerMascheroniConstant + Real.log (n : ℝ)) := (Real.exp_add _ _).symm
      _ < Real.exp (harmonic n : ℝ) := Real.exp_lt_exp.mpr hlog_add_lt
  have hH_pos : 0 < (harmonic n : ℝ) := by linarith
  have hmul :
      Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) <
        Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) :=
    mul_lt_mul'' hexp_lt hloglog_lt (by positivity) hloglog_pos.le
  linarith

/-- Elementary bridge from Robin's inequality to Lagarias's inequality for all `n > 5040`. -/
theorem lagarias_of_robin_of_gt_5040 (hR : RobinInequality) {n : ℕ} (hn : 5040 < n) :
    (ArithmeticFunction.sigma 1 n : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) :=
  le_of_lt (lt_trans (hR n hn) (robin_bound_lt_lagarias_bound (by omega)))

end RHDirect

end
