/-
MaynardDock — Wave 1 adapter.

Derives the `BombieriVinogradov` proposition consumed by the vendored
PrimeGapsTheory (AxiomMath/PrimeGapsLib) from the *unconditional* Bombieri–
Vinogradov theorem of `RHDirect.Stage11BombieriVinogradov`
(`rh_direct v1.2.0`, clone at ../alpoge-rh-golf).

Mathematical content.  Fix `0 < θ < 1/2` and `A ≥ 1`.  From
`RHDirect.bombieri_vinogradov (A + 8)` we obtain `Bv, Cv > 0` with

  ∑_{q ≤ ⌊√t / log^{Bv} t⌋}  max_{(a,q)=1} |ψ(t; q, a) − t/φ(q)| ≤ Cv·t/log^{A+8} t   (t ≥ 3).

Write `π(x; q, a)` for the AP prime count and `π(x)` for the global one.
The exact Abel identity (Stage10, `primeCountAP_eq_abel_thetaAP`)

  π(x; q, a) = θ(x; q, a)/log x + ∫₂ˣ θ(t; q, a)/(t log²t) dt

holds for both the AP counts (any `q ≥ 1`) and the global count (`q = 1`),
so the difference `π(x; q, a) − π(x)/φ(q)` is bounded by

  E(x)/log x + ∫₂ˣ E(t)/(t log²t) dt,   E(t) := |θ(t; q, a) − θ(t)/φ(q)|,

and `E` splits into the ψ-Bombieri–Vinogradov error (level covered below),
the prime-power gap `0 ≤ ψ − θ ≤ √t·log t` (uniform in `q, a`), and the
global ψ-error (the `q = 1` term of the same Bombieri–Vinogradov sum — no
separate PNT input is needed).

Level geometry.  Put `η := 1/2 − θ > 0` and `β := (1 + 2θ)/2 ∈ (1/2, 1)`.
Since `log^{Bv} t ≤ t^{η/8}` for all large `t` and `x^{2θ}·t^{η/8} ≤ t` once
`t ≥ x^β` (because `2θ/(1 − η/8) ≤ β < 1`), every modulus `q ≤ x^θ` lies in
the Bombieri–Vinogradov range `⌊√t/log^{Bv} t⌋` for all `t ≥ T₁(x) :=
max(t₀, x^β)`; below `T₁` the trivial class bound
`ψ(t; q, a) ≤ (t/q + 1)·log t` together with
`∑_{q ≤ Q} 1/q ≤ log Q + 1` and `∑_{q ≤ Q} 1/φ(q) ≤ 6·log 2Q` suffices,
contributing `x^{β}·polylog x = o(x/log^A x)`.
-/
import RHDirect.Stage11BombieriVinogradov
import RHDirect.Stage10SiegelWalfiszFull
import RHDirect.Stage4ExplicitFormula
import RHDirect.Stage5DirichletLZeroFree
import RHDirect.Stage8BarbanDavenport
import RHDirect.HostFieldSupply
import PrimeGapsTheory.NumberTheory.BombieriVinogradov

open RHDirect Nat Real Finset Filter MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

namespace MaynardDock

/-! ## Section 0: elementary bridges between the two libraries -/

/-- `RHDirect`'s AP prime count at modulus one is the global prime count. -/
theorem primeCountAP_one_eq (x : ℝ) :
    Stage2DirichletAP.primeCountAP 1 0 x = Nat.primeCounting ⌊x⌋₊ := by
  unfold Stage2DirichletAP.primeCountAP
  have hfil : (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ 0 [MOD 1]) =
      (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime :=
    Finset.filter_congr fun p _ => by simp [Nat.ModEq, Nat.mod_one]
  have hcard : ((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card = Nat.primeCounting ⌊x⌋₊ := by
    simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [hfil, hcard]

/-- An AP prime count is bounded by the global one. -/
theorem primeCountAP_le_global (q a : ℕ) (x : ℝ) :
    Stage2DirichletAP.primeCountAP q a x ≤ Nat.primeCounting ⌊x⌋₊ := by
  have hcard : ((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card = Nat.primeCounting ⌊x⌋₊ := by
    simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  calc Stage2DirichletAP.primeCountAP q a x
      = ((Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card := rfl
    _ ≤ ((Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime)).card :=
        Finset.card_le_card (by
          intro p hp
          simp only [Finset.mem_filter] at hp ⊢
          exact ⟨hp.1, hp.2.1⟩)
    _ = Nat.primeCounting ⌊x⌋₊ := hcard

/-- The `π(x; q, a')` of PrimeGapsTheory (for a natural representative `a'`)
is `RHDirect`'s `primeCountAP q a' x`. -/
theorem primeCountingZMod_eq_primeCountAP (x : ℝ) {q : ℕ} (a' : ℕ) :
    Real.primeCountingZMod x q (a' : ZMod q) = Stage2DirichletAP.primeCountAP q a' x := by
  rw [Real.primeCountingZMod_eq_card_finset_range]
  unfold Stage2DirichletAP.primeCountAP
  simp only [ZMod.natCast_eq_natCast_iff]

/-- A `ZMod` element equals the cast of its value. -/
theorem zmod_eq_val_cast {q : ℕ} [NeZero q] (a : ZMod q) : a = ((a.val : ℕ) : ZMod q) := by
  refine ZMod.val_injective q ?_
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt a)]

/-- Value of a unit is a coprime residue. -/
theorem unit_val_coprime {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) :
    Nat.Coprime (ZMod.val (n := q) (a : ZMod q)) q :=
  (ZMod.isUnit_iff_coprime (ZMod.val (n := q) (a : ZMod q)) q).mp
    (by rw [← zmod_eq_val_cast (a := (a : ZMod q))]; exact a.isUnit)

/-! ## Section 1: elementary analytic helpers -/

/-- Eventually `log^C x ≤ x^r` for any `C` and any `r > 0`. -/
theorem eventually_log_pow_le_rpow {C r : ℝ} (hr : 0 < r) :
    ∀ᶠ x : ℝ in Filter.atTop, (Real.log x) ^ C ≤ x ^ r := by
  have hone : ∀ x : ℝ, (1 : ℝ) ≤ x → (1 : ℝ) ≤ x ^ r := fun x hx => by
    calc (1 : ℝ) = (1 : ℝ) ^ r := (one_rpow r).symm
      _ ≤ x ^ r := rpow_le_rpow (by norm_num) hx (le_of_lt hr)
  have hone_lt_exp : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
  rcases lt_trichotomy C 0 with hC | rfl | hC
  · -- `C < 0`: `log^C x ≤ 1` once `log x ≥ 1`
    filter_upwards [eventually_ge_atTop (Real.exp 1 : ℝ)] with x hx
    have hexp : (Real.exp 1 : ℝ) ≤ x := hx
    have hlogpos : (1 : ℝ) ≤ Real.log x :=
      (Real.log_exp (1 : ℝ)).symm.trans_le (Real.log_le_log (Real.exp_pos 1) hexp)
    have hlognn : (0 : ℝ) ≤ Real.log x := le_trans zero_le_one hlogpos
    have hCpow : (Real.log x) ^ C ≤ 1 := by
      have hrw : (Real.log x) ^ C = ((Real.log x) ^ (-C))⁻¹ := by
        have h := rpow_neg hlognn (-C)
        simpa using h
      rw [hrw]
      have hpos : (0 : ℝ) < (Real.log x) ^ (-C) :=
        rpow_pos_of_pos (by linarith : (0 : ℝ) < Real.log x) (-C)
      have hbase : (1 : ℝ) ≤ (Real.log x) ^ (-C) :=
        calc (1 : ℝ) = (1 : ℝ) ^ (-C) := (one_rpow (-C)).symm
          _ ≤ (Real.log x) ^ (-C) :=
              rpow_le_rpow (by norm_num) hlogpos (le_of_lt (neg_pos.mpr hC))
      refine le_of_mul_le_mul_right ?_ hpos
      rw [inv_mul_cancel₀ hpos.ne', one_mul]
      exact hbase
    have hx1 : (1 : ℝ) ≤ x := by linarith [hexp, hone_lt_exp]
    exact hCpow.trans (hone x hx1)
  · -- `C = 0`
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [rpow_zero]
    exact hone x hx
  · -- `0 < C`: use `log x ≤ x ^ (r / C)` eventually
    obtain ⟨X, hX⟩ :=
      RHDirect.HostFieldSupply.mul_log_le_rpow_eventually (r / C) 1
        (by positivity : (0 : ℝ) < r / C) one_pos
    filter_upwards [eventually_ge_atTop (max (Real.exp 1 : ℝ) X)] with x hx
    have hmax : (max (Real.exp 1 : ℝ) X) ≤ x := hx
    have hexp : (Real.exp 1 : ℝ) ≤ x := le_trans (le_max_left _ _) hmax
    have hxX : X ≤ x := le_trans (le_max_right _ _) hmax
    have hx1 : (1 : ℝ) ≤ x := by linarith [hexp, hone_lt_exp]
    have hlognn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith [hone_lt_exp])
    have hX' : 1 * Real.log x ≤ x ^ (r / C) := hX x hxX
    have hmono : (Real.log x) ^ C ≤ (x ^ (r / C)) ^ C :=
      rpow_le_rpow hlognn (by rw [one_mul] at hX'; exact hX') (le_of_lt hC)
    rw [← rpow_mul (by linarith : (0 : ℝ) ≤ x) (r / C) C] at hmono
    calc (Real.log x) ^ C ≤ x ^ (r / C * C) := hmono
      _ = x ^ r := by rw [show r / C * C = r by field_simp]

/-- Elementary residue-class counting bound. -/
theorem card_le_class_count {q : ℕ} (_hq : 0 < q) (a t : ℕ) :
    ((Finset.range (t + 1)).filter (fun n => n ≡ a [MOD q])).card ≤ t / q + 1 := by
  classical
  have hinj : ∀ n ∈ (Finset.range (t + 1)).filter (fun n => n ≡ a [MOD q]),
      ∀ m ∈ (Finset.range (t + 1)).filter (fun n => n ≡ a [MOD q]),
      n / q = m / q → n = m := by
    intro n hn m hm hdiv
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hn hm
    have hn2 : n % q = a % q := hn.2
    have hm2 : m % q = a % q := hm.2
    have hn' : n = q * (n / q) + a % q := by
      have h := Nat.div_add_mod n q
      rw [hn2] at h
      exact h.symm
    have hm' : m = q * (m / q) + a % q := by
      have h := Nat.div_add_mod m q
      rw [hm2] at h
      exact h.symm
    rw [hn', hm', hdiv]
  have himg : ∀ n ∈ (Finset.range (t + 1)).filter (fun n => n ≡ a [MOD q]),
      n / q < t / q + 1 := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hn
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hn.1)
  calc ((Finset.range (t + 1)).filter (fun n => n ≡ a [MOD q])).card
      = (((Finset.range (t + 1)).filter (fun n => n ≡ a [MOD q])).image
          (fun n => n / q)).card :=
        (Finset.card_image_of_injOn
          (fun n hn m hm h => hinj n (Finset.mem_coe.mp hn) m (Finset.mem_coe.mp hm) h)).symm
    _ ≤ (Finset.range (t / q + 1)).card :=
        Finset.card_le_card (Finset.subset_range.mpr (fun n hn => by
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
          exact himg m hm))
    _ = t / q + 1 := Finset.card_range _

/-! ## Section 2: Abel machinery -/

/-- Modulus-one `ψ_AP` is the global `ψ`. -/
theorem chebyshevPsiAP_one (t : ℝ) :
    Stage2DirichletAP.chebyshevPsiAP 1 0 t = RHDirect.chebyshevPsi t := by
  unfold Stage2DirichletAP.chebyshevPsiAP RHDirect.chebyshevPsi
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Nat.ModEq, Nat.mod_one, if_true]

/-- Modulus-one `θ_AP` is the global `θ`. -/
theorem chebyshevThetaAP_one (t : ℝ) :
    Stage2DirichletAP.chebyshevThetaAP 1 0 t = RHDirect.Stage2DirichletAP.chebyshevTheta t := by
  unfold Stage2DirichletAP.chebyshevThetaAP Stage2DirichletAP.chebyshevTheta
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Nat.ModEq, Nat.mod_one, and_true]

/-- The global `ψ`-error is controlled by the `q = 1` term of the Bombieri–Vinogradov sum. -/
theorem abs_chebyshevPsi_sub_le_psiAPMaxError_one (t : ℝ) :
    |RHDirect.chebyshevPsi t - t| ≤ Stage11BombieriVinogradov.psiAPMaxError 1 t := by
  have h := Stage11BombieriVinogradov.abs_chebyshevPsiAP_sub_le_psiAPMaxError
    (q := 1) (a := 0) one_pos (by simp : Nat.Coprime 0 1) t
  rwa [chebyshevPsiAP_one, show ((Nat.totient 1 : ℕ) : ℝ) = 1 by simp, div_one] at h

/-- Trivial bound: any `ψ_AP` is at most the global `ψ`. -/
theorem chebyshevPsiAP_le_global (q a : ℕ) (t : ℝ) :
    Stage2DirichletAP.chebyshevPsiAP q a t ≤ RHDirect.chebyshevPsi t := by
  unfold Stage2DirichletAP.chebyshevPsiAP RHDirect.chebyshevPsi
  refine Finset.sum_le_sum fun n _ => ?_
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

/-- Trivial bound: any `θ_AP` is at most `6t`. -/
theorem chebyshevThetaAP_le_six_mul (q a : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    Stage2DirichletAP.chebyshevThetaAP q a t ≤ 6 * t := by
  exact le_trans (Stage2DirichletAP.chebyshevThetaAP_le_chebyshevPsiAP q a t)
    (le_trans (chebyshevPsiAP_le_global q a t) (Stage4ExplicitFormula.chebyshevPsi_le_six_mul ht))

/-- Trivial bound: the global `θ` is at most `6t`. -/
theorem chebyshevTheta_le_six_mul {t : ℝ} (ht : 1 ≤ t) :
    RHDirect.Stage2DirichletAP.chebyshevTheta t ≤ 6 * t := by
  rw [← chebyshevThetaAP_one]
  exact chebyshevThetaAP_le_six_mul 1 0 ht

/-- Measurability of `θ_AP` (step function through `Nat.floor`). -/
theorem measurable_chebyshevThetaAP' (q a : ℕ) :
    Measurable (fun t : ℝ => Stage2DirichletAP.chebyshevThetaAP q a t) := by
  have h : (fun t : ℝ => Stage2DirichletAP.chebyshevThetaAP q a t) =
      (fun k : ℕ => ∑ n ∈ Finset.range (k + 1),
        if n.Prime ∧ n ≡ a [MOD q] then Real.log (n : ℝ) else 0) ∘ Nat.floor := rfl
  rw [h]
  exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor

/-- Measurability of the global `θ`. -/
theorem measurable_chebyshevTheta' :
    Measurable (fun t : ℝ => RHDirect.Stage2DirichletAP.chebyshevTheta t) := by
  have h : (fun t : ℝ => RHDirect.Stage2DirichletAP.chebyshevTheta t) =
      (fun t : ℝ => Stage2DirichletAP.chebyshevThetaAP 1 0 t) := by
    funext t; exact (chebyshevThetaAP_one t).symm
  rw [h]
  exact measurable_chebyshevThetaAP' 1 0

/-- Measurability of `ψ_AP` (step function through `Nat.floor`). -/
theorem measurable_chebyshevPsiAP' (q a : ℕ) :
    Measurable (fun t : ℝ => Stage2DirichletAP.chebyshevPsiAP q a t) := by
  have h : (fun t : ℝ => Stage2DirichletAP.chebyshevPsiAP q a t) =
      (fun k : ℕ => ∑ n ∈ Finset.range (k + 1), if n ≡ a [MOD q] then Λ n else 0) ∘ Nat.floor := rfl
  rw [h]
  exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor

/-- Measurability of a finite pointwise supremum. -/
private theorem measurable_finset_sup' {ι : Type*} (s : Finset ι)
    (F : ι → ℝ → ℝ) (hF : ∀ i ∈ s, Measurable (F i)) :
    ∀ hne : s.Nonempty, Measurable (fun t => s.sup' hne (fun i => F i t)) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro hne; exact absurd hne (by simp)
  | insert a s ha ih =>
    intro hne
    have hf : Measurable (F a) := hF a (Finset.mem_insert_self _ _)
    have hfS : ∀ i ∈ s, Measurable (F i) := fun i hi => hF i (Finset.mem_insert_of_mem hi)
    rcases Finset.eq_empty_or_nonempty s with rfl | hs
    · -- `s = ∅`: the supremum over `{a}` is `F a`
      have hfun : (fun t => (insert a (∅ : Finset ι)).sup' hne (fun i => F i t)) = F a := by
        funext t
        have hle : (insert a (∅ : Finset ι)).sup' hne (fun i => F i t) ≤ F a t :=
          Finset.sup'_le hne (fun i => F i t) (fun b hb => by
            rcases Finset.mem_insert.1 hb with rfl | hb'
            · exact le_rfl
            · exact absurd hb' (by simp))
        have hge : F a t ≤ (insert a (∅ : Finset ι)).sup' hne (fun i => F i t) :=
          Finset.le_sup' (fun i => F i t) (Finset.mem_insert_self a ∅)
        exact le_antisymm hle hge
      rw [hfun]
      exact hf
    · -- `s` nonempty: sup' over `insert a s` is the pointwise max
      have hcast : (fun t => (insert a s).sup' hne (fun i => F i t)) =
          (fun t => (insert a s).sup' (Finset.insert_nonempty a s) (fun i => F i t)) := rfl
      rw [hcast]
      simp only [Finset.sup'_insert hs]
      exact hf.max (ih hfS hs)

/-- Measurability of `psiAPMaxError` in its second argument. -/
theorem measurable_psiAPMaxError (q : ℕ) :
    Measurable (fun t : ℝ => Stage11BombieriVinogradov.psiAPMaxError q t) := by
  classical
  by_cases hne : ((Finset.range q).filter (fun a => Nat.Coprime a q)).Nonempty
  · have hfun : ∀ t : ℝ, Stage11BombieriVinogradov.psiAPMaxError q t =
      ((Finset.range q).filter (fun a => Nat.Coprime a q)).sup' hne
        (fun a => |Stage2DirichletAP.chebyshevPsiAP q a t - t / ((q.totient : ℕ) : ℝ)|) :=
      fun _ => dif_pos hne
    simp only [hfun]
    refine measurable_finset_sup' _ (fun a t =>
      |Stage2DirichletAP.chebyshevPsiAP q a t - t / ((q.totient : ℕ) : ℝ)|) ?_ hne
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    exact (continuous_abs).measurable.comp
      ((measurable_chebyshevPsiAP' q a).sub (measurable_id.div_const _))
  · have hfun : ∀ t : ℝ, Stage11BombieriVinogradov.psiAPMaxError q t = 0 :=
      fun _ => dif_neg hne
    simp only [hfun]
    exact measurable_const

/-! ## Section 3: class refinement and the `θ`-error decomposition -/

/-- Refined class bound: `ψ(t; q, a) ≤ (t/q + 1)·log t` for `t ≥ 2`. -/
theorem chebyshevPsiAP_le_class {q : ℕ} (hq : 0 < q) (a' : ℕ) {t : ℝ} (ht : 2 ≤ t) :
    Stage2DirichletAP.chebyshevPsiAP q a' t ≤ (t / (q : ℝ) + 1) * Real.log t := by
  classical
  have hΛ : ∀ n ∈ (Finset.range (⌊t⌋₊ + 1)).filter (fun n => n ≡ a' [MOD q]),
      Λ n ≤ Real.log t := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hn
    have hnle : n ≤ t :=
      le_trans (by exact_mod_cast hn.1) (Nat.floor_le (by linarith))
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have h0 : (Λ (0 : ℕ) : ℝ) ≤ (0 : ℝ) := by simp
      exact le_trans h0 (Real.log_nonneg (by linarith : (1 : ℝ) ≤ t))
    · exact le_trans ArithmeticFunction.vonMangoldt_le_log
        (Real.log_le_log (by positivity) hnle)
  have hmem : ∀ n ∈ (Finset.range (⌊t⌋₊ + 1)).filter (fun n => n ≡ a' [MOD q]),
      (if n ≡ a' [MOD q] then (Λ n : ℝ) else 0) = Λ n :=
    fun n hn => if_pos (Finset.mem_filter.mp hn).2
  have hnotmem : ∀ n ∈ (Finset.range (⌊t⌋₊ + 1)).filter (fun n => ¬ n ≡ a' [MOD q]),
      (if n ≡ a' [MOD q] then (Λ n : ℝ) else 0) = 0 :=
    fun n hn => if_neg (Finset.mem_filter.mp hn).2
  have hdisj : Disjoint
      ((Finset.range (⌊t⌋₊ + 1)).filter (fun n => n ≡ a' [MOD q]))
      ((Finset.range (⌊t⌋₊ + 1)).filter (fun n => ¬ n ≡ a' [MOD q])) := by
    rw [Finset.disjoint_right]
    intro a ha ha'
    simp only [Finset.mem_filter] at ha ha'
    first
    | exact ha'.2 ha.2
    | exact ha.2 ha'.2
  have hunion : (Finset.range (⌊t⌋₊ + 1)).filter (fun n => n ≡ a' [MOD q]) ∪
      (Finset.range (⌊t⌋₊ + 1)).filter (fun n => ¬ n ≡ a' [MOD q]) =
      Finset.range (⌊t⌋₊ + 1) := by
    ext n
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hn : n ≡ a' [MOD q] <;> simp [hn]
  have hfloort : (0 : ℝ) ≤ Real.log t := Real.log_nonneg (by linarith : (1 : ℝ) ≤ t)
  calc Stage2DirichletAP.chebyshevPsiAP q a' t
      = ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (if n ≡ a' [MOD q] then (Λ n : ℝ) else 0) := rfl
    _ = (∑ n ∈ (Finset.range (⌊t⌋₊ + 1)).filter (fun n => n ≡ a' [MOD q]),
          (if n ≡ a' [MOD q] then (Λ n : ℝ) else 0)) +
        (∑ n ∈ (Finset.range (⌊t⌋₊ + 1)).filter (fun n => ¬ n ≡ a' [MOD q]),
          (if n ≡ a' [MOD q] then (Λ n : ℝ) else 0)) := by
          rw [← Finset.sum_union hdisj, hunion]
    _ = ∑ n ∈ (Finset.range (⌊t⌋₊ + 1)).filter (fun n => n ≡ a' [MOD q]), (Λ n : ℝ) := by
          rw [Finset.sum_congr rfl hmem, Finset.sum_congr rfl hnotmem, Finset.sum_const_zero,
            add_zero]
    _ ≤ ∑ n ∈ (Finset.range (⌊t⌋₊ + 1)).filter (fun n => n ≡ a' [MOD q]), Real.log t :=
        Finset.sum_le_sum hΛ
    _ = ((Finset.range (⌊t⌋₊ + 1)).filter (fun n => n ≡ a' [MOD q])).card * Real.log t := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((⌊t⌋₊ / q : ℕ) : ℝ) + 1) * Real.log t := by
        refine mul_le_mul_of_nonneg_right ?_ hfloort
        exact_mod_cast card_le_class_count hq a' ⌊t⌋₊
    _ ≤ (t / (q : ℝ) + 1) * Real.log t := by
        refine mul_le_mul_of_nonneg_right ?_ hfloort
        have h1 : ((⌊t⌋₊ / q : ℕ) : ℝ) ≤ (⌊t⌋₊ : ℝ) / (q : ℝ) := Nat.cast_div_le
        have h2 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
        have h3 : (⌊t⌋₊ : ℝ) / (q : ℝ) ≤ t / (q : ℝ) :=
          div_le_div_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ (q : ℝ))
        linarith

/-- Pointwise `θ`-error decomposition into `ψ`-errors and prime-power gaps. -/
theorem abs_thetaAP_sub_theta_div_le {q : ℕ} (hq : 0 < q) (a' : ℕ) (hcop : Nat.Coprime a' q)
    {t : ℝ} (ht : 1 ≤ t) :
    |Stage2DirichletAP.chebyshevThetaAP q a' t -
        RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)| ≤
      Stage11BombieriVinogradov.psiAPMaxError q t + Real.sqrt t * Real.log t +
      (Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) /
        ((q.totient : ℕ) : ℝ) := by
  have hphi_pos : (0 : ℝ) < ((q.totient : ℕ) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hθAP_le : Stage2DirichletAP.chebyshevThetaAP q a' t ≤
      Stage2DirichletAP.chebyshevPsiAP q a' t :=
    Stage2DirichletAP.chebyshevThetaAP_le_chebyshevPsiAP q a' t
  have hppAP : Stage2DirichletAP.chebyshevPsiAP q a' t - Stage2DirichletAP.chebyshevThetaAP q a' t ≤
      Real.sqrt t * Real.log t := Stage2DirichletAP.chebyshevPsiAP_sub_chebyshevThetaAP_le q a' ht
  have hppG : RHDirect.chebyshevPsi t - RHDirect.Stage2DirichletAP.chebyshevTheta t ≤
      Real.sqrt t * Real.log t :=
    (Stage2DirichletAP.chebyshevPsi_sub_chebyshevTheta_bounds ht).2
  have hψerr : |Stage2DirichletAP.chebyshevPsiAP q a' t - t / ((q.totient : ℕ) : ℝ)| ≤
      Stage11BombieriVinogradov.psiAPMaxError q t :=
    Stage11BombieriVinogradov.abs_chebyshevPsiAP_sub_le_psiAPMaxError hq hcop t
  have hψerrG : |RHDirect.chebyshevPsi t - t| ≤ Stage11BombieriVinogradov.psiAPMaxError 1 t :=
    abs_chebyshevPsi_sub_le_psiAPMaxError_one t
  have hkey : Stage2DirichletAP.chebyshevThetaAP q a' t -
      RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ) =
      (Stage2DirichletAP.chebyshevPsiAP q a' t - t / ((q.totient : ℕ) : ℝ)) +
      (Stage2DirichletAP.chebyshevThetaAP q a' t - Stage2DirichletAP.chebyshevPsiAP q a' t) +
      (t - RHDirect.chebyshevPsi t) / ((q.totient : ℕ) : ℝ) +
      (RHDirect.chebyshevPsi t - RHDirect.Stage2DirichletAP.chebyshevTheta t) /
        ((q.totient : ℕ) : ℝ) := by
    field_simp [hphi_pos.ne']
    ring
  rw [hkey]
  have hθAP_le' : Stage2DirichletAP.chebyshevThetaAP q a' t -
      Stage2DirichletAP.chebyshevPsiAP q a' t ≤ 0 := sub_nonpos.mpr hθAP_le
  have h1 : |Stage2DirichletAP.chebyshevPsiAP q a' t - t / ((q.totient : ℕ) : ℝ)| ≤
      Stage11BombieriVinogradov.psiAPMaxError q t := hψerr
  have h2 : |Stage2DirichletAP.chebyshevThetaAP q a' t - Stage2DirichletAP.chebyshevPsiAP q a' t| ≤
      Real.sqrt t * Real.log t := by
    rw [abs_of_nonpos hθAP_le']
    linarith
  have h3 : |(t - RHDirect.chebyshevPsi t) / ((q.totient : ℕ) : ℝ)| ≤
      Stage11BombieriVinogradov.psiAPMaxError 1 t / ((q.totient : ℕ) : ℝ) := by
    rw [abs_div, abs_of_pos hphi_pos, abs_sub_comm]
    exact div_le_div_of_nonneg_right hψerrG hphi_pos.le
  have h4 : |(RHDirect.chebyshevPsi t - RHDirect.Stage2DirichletAP.chebyshevTheta t) /
      ((q.totient : ℕ) : ℝ)| ≤ Real.sqrt t * Real.log t / ((q.totient : ℕ) : ℝ) := by
    rw [abs_div, abs_of_pos hphi_pos,
      abs_of_nonneg (Stage2DirichletAP.chebyshevPsi_sub_chebyshevTheta_bounds ht).1]
    exact div_le_div_of_nonneg_right hppG hphi_pos.le
  have htri : |((Stage2DirichletAP.chebyshevPsiAP q a' t - t / ((q.totient : ℕ) : ℝ) +
        (Stage2DirichletAP.chebyshevThetaAP q a' t - Stage2DirichletAP.chebyshevPsiAP q a' t)) +
      (t - RHDirect.chebyshevPsi t) / ((q.totient : ℕ) : ℝ)) +
      (RHDirect.chebyshevPsi t - RHDirect.Stage2DirichletAP.chebyshevTheta t) /
        ((q.totient : ℕ) : ℝ)| ≤
      |Stage2DirichletAP.chebyshevPsiAP q a' t - t / ((q.totient : ℕ) : ℝ)| +
      |Stage2DirichletAP.chebyshevThetaAP q a' t - Stage2DirichletAP.chebyshevPsiAP q a' t| +
      |(t - RHDirect.chebyshevPsi t) / ((q.totient : ℕ) : ℝ)| +
      |(RHDirect.chebyshevPsi t - RHDirect.Stage2DirichletAP.chebyshevTheta t) /
        ((q.totient : ℕ) : ℝ)| := by
    calc |((Stage2DirichletAP.chebyshevPsiAP q a' t - t / ((q.totient : ℕ) : ℝ) +
          (Stage2DirichletAP.chebyshevThetaAP q a' t - Stage2DirichletAP.chebyshevPsiAP q a' t)) +
        (t - RHDirect.chebyshevPsi t) / ((q.totient : ℕ) : ℝ)) +
        (RHDirect.chebyshevPsi t - RHDirect.Stage2DirichletAP.chebyshevTheta t) /
          ((q.totient : ℕ) : ℝ)|
        ≤ |(Stage2DirichletAP.chebyshevPsiAP q a' t - t / ((q.totient : ℕ) : ℝ) +
            (Stage2DirichletAP.chebyshevThetaAP q a' t - Stage2DirichletAP.chebyshevPsiAP q a' t)) +
          (t - RHDirect.chebyshevPsi t) / ((q.totient : ℕ) : ℝ)| +
          |(RHDirect.chebyshevPsi t - RHDirect.Stage2DirichletAP.chebyshevTheta t) /
            ((q.totient : ℕ) : ℝ)| := abs_add_le (α := ℝ) _ _
      _ ≤ (|Stage2DirichletAP.chebyshevPsiAP q a' t - t / ((q.totient : ℕ) : ℝ) +
            (Stage2DirichletAP.chebyshevThetaAP q a' t - Stage2DirichletAP.chebyshevPsiAP q a' t)| +
          |(t - RHDirect.chebyshevPsi t) / ((q.totient : ℕ) : ℝ)|) +
          |(RHDirect.chebyshevPsi t - RHDirect.Stage2DirichletAP.chebyshevTheta t) /
            ((q.totient : ℕ) : ℝ)| := by
          exact add_le_add_left
            (abs_add_le (α := ℝ) _ _) _
      _ ≤ ((|Stage2DirichletAP.chebyshevPsiAP q a' t - t / ((q.totient : ℕ) : ℝ)| +
            |Stage2DirichletAP.chebyshevThetaAP q a' t - Stage2DirichletAP.chebyshevPsiAP q a' t|) +
          |(t - RHDirect.chebyshevPsi t) / ((q.totient : ℕ) : ℝ)|) +
          |(RHDirect.chebyshevPsi t - RHDirect.Stage2DirichletAP.chebyshevTheta t) /
            ((q.totient : ℕ) : ℝ)| := by
          exact add_le_add_left
            (add_le_add_left (abs_add_le (α := ℝ) _ _) _) _
  have hfin : |Stage2DirichletAP.chebyshevPsiAP q a' t - t / ((q.totient : ℕ) : ℝ)| +
      |Stage2DirichletAP.chebyshevThetaAP q a' t - Stage2DirichletAP.chebyshevPsiAP q a' t| +
      |(t - RHDirect.chebyshevPsi t) / ((q.totient : ℕ) : ℝ)| +
      |(RHDirect.chebyshevPsi t - RHDirect.Stage2DirichletAP.chebyshevTheta t) /
        ((q.totient : ℕ) : ℝ)| ≤
      Stage11BombieriVinogradov.psiAPMaxError q t + Real.sqrt t * Real.log t +
      (Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) /
        ((q.totient : ℕ) : ℝ) := by
    rw [add_div]
    linarith
  exact le_trans htri hfin

/-! ## Section 4: the Abel assembly -/

/-- Integrability of the merged `θ`-error integrand on `[u, v] ⊆ [2, ∞)`. -/
theorem intervalIntegrable_theta_err {q : ℕ} (hq : 0 < q) (a' : ℕ) {u v : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) :
    IntervalIntegrable (fun t : ℝ =>
      (Stage2DirichletAP.chebyshevThetaAP q a' t -
        RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)) /
      (t * (Real.log t) ^ 2)) volume u v := by
  have hφ : (1 : ℝ) ≤ ((q.totient : ℕ) : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hθnonneg : ∀ t : ℝ, (0 : ℝ) ≤ RHDirect.Stage2DirichletAP.chebyshevTheta t := by
    intro t
    rw [← chebyshevThetaAP_one t]
    exact Stage2DirichletAP.chebyshevThetaAP_nonneg 1 0 t
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mpr ?_
  refine Integrable.mono'
    (integrableOn_const (C := 12 / (Real.log 2) ^ 2) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
  · exact (((measurable_chebyshevThetaAP' q a').sub
      ((measurable_chebyshevTheta').div_const _)).div
      (measurable_id.mul (Real.measurable_log.pow_const 2))).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
    have ht2 : 2 ≤ t := hu.trans ht.1.le
    have ht0 : (0 : ℝ) < t := by linarith
    have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
    have hlt_pos : (0 : ℝ) < Real.log t := hlog2.trans_le hlt
    have h1 : Stage2DirichletAP.chebyshevThetaAP q a' t ≤ 6 * t :=
      chebyshevThetaAP_le_six_mul q a' (by linarith : (1 : ℝ) ≤ t)
    have h2 : RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ) ≤ 6 * t := by
      have hθ : RHDirect.Stage2DirichletAP.chebyshevTheta t ≤ 6 * t :=
        chebyshevTheta_le_six_mul (by linarith : (1 : ℝ) ≤ t)
      have hdiv : RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ) ≤
          (6 * t) / ((q.totient : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hθ (by positivity : (0 : ℝ) ≤ ((q.totient : ℕ) : ℝ))
      have h6φ : (6 * t) / ((q.totient : ℕ) : ℝ) ≤ 6 * t := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((q.totient : ℕ) : ℝ))]
        nlinarith [hφ]
      linarith
    have h3 : (0 : ℝ) ≤ Stage2DirichletAP.chebyshevThetaAP q a' t :=
      Stage2DirichletAP.chebyshevThetaAP_nonneg q a' t
    have h4 : (0 : ℝ) ≤ RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ) :=
      div_nonneg (hθnonneg t) (by positivity : (0 : ℝ) ≤ ((q.totient : ℕ) : ℝ))
    have hbound : |Stage2DirichletAP.chebyshevThetaAP q a' t -
        RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)| ≤ 12 * t := by
      rw [abs_le]; constructor <;> nlinarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos ht0 (sq_pos_of_pos hlt_pos))]
    calc |Stage2DirichletAP.chebyshevThetaAP q a' t -
          RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)| /
          (t * (Real.log t) ^ 2)
        ≤ (12 * t) / (t * (Real.log 2) ^ 2) := by
          refine div_le_div₀ (by positivity) hbound (by positivity) ?_
          gcongr
      _ = 12 / (Real.log 2) ^ 2 := by field_simp [ht0.ne']

/-- Integrability of the unscaled global `θ`-integrand on `[u, v] ⊆ [2, ∞)`. -/
theorem intervalIntegrable_theta {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    IntervalIntegrable (fun t : ℝ =>
      RHDirect.Stage2DirichletAP.chebyshevTheta t / (t * (Real.log t) ^ 2)) volume u v := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hθnonneg : ∀ t : ℝ, (0 : ℝ) ≤ RHDirect.Stage2DirichletAP.chebyshevTheta t := by
    intro t
    rw [← chebyshevThetaAP_one t]
    exact Stage2DirichletAP.chebyshevThetaAP_nonneg 1 0 t
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mpr ?_
  refine Integrable.mono'
    (integrableOn_const (C := 6 / (Real.log 2) ^ 2) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
  · exact ((measurable_chebyshevTheta').div
      (measurable_id.mul (Real.measurable_log.pow_const 2))).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
    have ht2 : 2 ≤ t := hu.trans ht.1.le
    have ht0 : (0 : ℝ) < t := by linarith
    have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
    have hlt_pos : (0 : ℝ) < Real.log t := hlog2.trans_le hlt
    have h2 : RHDirect.Stage2DirichletAP.chebyshevTheta t ≤ 6 * t :=
      chebyshevTheta_le_six_mul (by linarith : (1 : ℝ) ≤ t)
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (hθnonneg t),
      abs_of_pos (mul_pos ht0 (sq_pos_of_pos hlt_pos))]
    calc RHDirect.Stage2DirichletAP.chebyshevTheta t / (t * (Real.log t) ^ 2)
        ≤ (6 * t) / (t * (Real.log 2) ^ 2) := by
          refine div_le_div₀ (by positivity) h2 (by positivity) ?_
          gcongr
      _ = 6 / (Real.log 2) ^ 2 := by field_simp [ht0.ne']

/-- **The Abel assembly**: `π(x; q, a') − π(x)/φ(q)` is bounded by the merged
`θ`-error at `x` over `log x` plus its integral against `dt/(t log²t)`. -/
theorem abel_diff_le {q : ℕ} (hq : 0 < q) (a' : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    |(Stage2DirichletAP.primeCountAP q a' x : ℝ) - _root_.pi x / ((q.totient : ℕ) : ℝ)| ≤
      |Stage2DirichletAP.chebyshevThetaAP q a' x -
        RHDirect.Stage2DirichletAP.chebyshevTheta x / ((q.totient : ℕ) : ℝ)| / Real.log x +
      ∫ t in (2 : ℝ)..x, |Stage2DirichletAP.chebyshevThetaAP q a' t -
        RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)| /
        (t * (Real.log t) ^ 2) := by
  have hφpos : (0 : ℝ) < ((q.totient : ℕ) : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith : (1 : ℝ) < x)
  have hintG : IntervalIntegrable (fun t : ℝ =>
      RHDirect.Stage2DirichletAP.chebyshevTheta t / (t * (Real.log t) ^ 2)) volume (2 : ℝ) x :=
    intervalIntegrable_theta (le_rfl (a := (2 : ℝ))) hx
  have hintG' : IntervalIntegrable (fun t : ℝ =>
      ((q.totient : ℕ) : ℝ)⁻¹ *
        (RHDirect.Stage2DirichletAP.chebyshevTheta t / (t * (Real.log t) ^ 2))) volume (2 : ℝ) x :=
    hintG.const_mul _
  have hintM : IntervalIntegrable (fun t : ℝ =>
      (Stage2DirichletAP.chebyshevThetaAP q a' t -
        RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)) /
      (t * (Real.log t) ^ 2)) volume (2 : ℝ) x :=
    intervalIntegrable_theta_err hq a' (le_rfl (a := (2 : ℝ))) hx
  have hintAP : IntervalIntegrable (fun t : ℝ =>
      Stage2DirichletAP.chebyshevThetaAP q a' t / (t * (Real.log t) ^ 2)) volume (2 : ℝ) x := by
    have heq : (fun t : ℝ => Stage2DirichletAP.chebyshevThetaAP q a' t /
        (t * (Real.log t) ^ 2)) =
        (fun t : ℝ => (Stage2DirichletAP.chebyshevThetaAP q a' t -
          RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)) /
          (t * (Real.log t) ^ 2) +
          ((q.totient : ℕ) : ℝ)⁻¹ *
            (RHDirect.Stage2DirichletAP.chebyshevTheta t / (t * (Real.log t) ^ 2))) := by
      funext t
      field_simp [hφpos.ne']
      ring
    rw [heq]
    exact hintM.add hintG'
  -- The merged integral identity:
  have hmerge : (∫ t in (2 : ℝ)..x, Stage2DirichletAP.chebyshevThetaAP q a' t /
        (t * (Real.log t) ^ 2)) -
      ((q.totient : ℕ) : ℝ)⁻¹ * (∫ t in (2 : ℝ)..x,
        RHDirect.Stage2DirichletAP.chebyshevTheta t / (t * (Real.log t) ^ 2)) =
      ∫ t in (2 : ℝ)..x, (Stage2DirichletAP.chebyshevThetaAP q a' t -
          RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)) /
        (t * (Real.log t) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul ((q.totient : ℕ) : ℝ)⁻¹
        (fun t : ℝ => RHDirect.Stage2DirichletAP.chebyshevTheta t /
          (t * (Real.log t) ^ 2)),
      ← intervalIntegral.integral_sub hintAP hintG']
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hx] at ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have ht0 : (0 : ℝ) < t := by linarith
    have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
    have hlt_pos : (0 : ℝ) < Real.log t := (Real.log_pos (by norm_num)).trans_le hlt
    field_simp [hφpos.ne', ht0.ne', hlt_pos.ne']
  -- The two Abel identities:
  have hAP := Stage10SiegelWalfiszFull.primeCountAP_eq_abel_thetaAP q a' hx
  have hG0 := Stage10SiegelWalfiszFull.primeCountAP_eq_abel_thetaAP 1 0 hx
  simp only [chebyshevThetaAP_one] at hG0
  rw [primeCountAP_one_eq x] at hG0
  rw [hAP, show _root_.pi x = ((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) from rfl, hG0, add_div,
    sub_add_eq_sub_sub]
  -- Shape normalization with identical integral atoms on both sides:
  have hshape :
      (Stage2DirichletAP.chebyshevThetaAP q a' x / Real.log x +
        ∫ t in (2 : ℝ)..x, Stage2DirichletAP.chebyshevThetaAP q a' t /
          (t * (Real.log t) ^ 2)) -
      RHDirect.Stage2DirichletAP.chebyshevTheta x / Real.log x / ((q.totient : ℕ) : ℝ) -
      (∫ t in (2 : ℝ)..x, RHDirect.Stage2DirichletAP.chebyshevTheta t /
          (t * (Real.log t) ^ 2)) / ((q.totient : ℕ) : ℝ) =
      (Stage2DirichletAP.chebyshevThetaAP q a' x -
        RHDirect.Stage2DirichletAP.chebyshevTheta x / ((q.totient : ℕ) : ℝ)) / Real.log x +
      ((∫ t in (2 : ℝ)..x, Stage2DirichletAP.chebyshevThetaAP q a' t /
          (t * (Real.log t) ^ 2)) -
        (∫ t in (2 : ℝ)..x, RHDirect.Stage2DirichletAP.chebyshevTheta t /
          (t * (Real.log t) ^ 2)) / ((q.totient : ℕ) : ℝ)) := by
    field_simp [hφpos.ne', hlogx.ne']
    ring
  rw [hshape]
  have hmerge' : (∫ t in (2 : ℝ)..x, Stage2DirichletAP.chebyshevThetaAP q a' t /
        (t * (Real.log t) ^ 2)) -
      (∫ t in (2 : ℝ)..x, RHDirect.Stage2DirichletAP.chebyshevTheta t /
        (t * (Real.log t) ^ 2)) / ((q.totient : ℕ) : ℝ) =
      ∫ t in (2 : ℝ)..x, (Stage2DirichletAP.chebyshevThetaAP q a' t -
          RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)) /
        (t * (Real.log t) ^ 2) := by
    rw [show ((∫ t in (2 : ℝ)..x, RHDirect.Stage2DirichletAP.chebyshevTheta t /
          (t * (Real.log t) ^ 2)) / ((q.totient : ℕ) : ℝ)) =
        ((q.totient : ℕ) : ℝ)⁻¹ * (∫ t in (2 : ℝ)..x,
          RHDirect.Stage2DirichletAP.chebyshevTheta t / (t * (Real.log t) ^ 2)) from by ring,
      hmerge]
  rw [hmerge']
  calc |(Stage2DirichletAP.chebyshevThetaAP q a' x -
          RHDirect.Stage2DirichletAP.chebyshevTheta x / ((q.totient : ℕ) : ℝ)) / Real.log x +
        ∫ t in (2 : ℝ)..x, (Stage2DirichletAP.chebyshevThetaAP q a' t -
          RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)) /
          (t * (Real.log t) ^ 2)|
      ≤ |(Stage2DirichletAP.chebyshevThetaAP q a' x -
            RHDirect.Stage2DirichletAP.chebyshevTheta x / ((q.totient : ℕ) : ℝ)) / Real.log x| +
        |∫ t in (2 : ℝ)..x, (Stage2DirichletAP.chebyshevThetaAP q a' t -
            RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)) /
            (t * (Real.log t) ^ 2)| := abs_add_le _ _
    _ ≤ |Stage2DirichletAP.chebyshevThetaAP q a' x -
          RHDirect.Stage2DirichletAP.chebyshevTheta x / ((q.totient : ℕ) : ℝ)| / Real.log x +
        ∫ t in (2 : ℝ)..x, |Stage2DirichletAP.chebyshevThetaAP q a' t -
          RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)| /
          (t * (Real.log t) ^ 2) := by
        refine add_le_add ?_ ?_
        · rw [abs_div, abs_of_pos hlogx]
        · calc |∫ t in (2 : ℝ)..x, (Stage2DirichletAP.chebyshevThetaAP q a' t -
                RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)) /
                (t * (Real.log t) ^ 2)|
              ≤ ∫ t in (2 : ℝ)..x, |(Stage2DirichletAP.chebyshevThetaAP q a' t -
                  RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)) /
                  (t * (Real.log t) ^ 2)| :=
                intervalIntegral.abs_integral_le_integral_abs hx
            _ = ∫ t in (2 : ℝ)..x, |Stage2DirichletAP.chebyshevThetaAP q a' t -
                  RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)| /
                  (t * (Real.log t) ^ 2) := by
                refine intervalIntegral.integral_congr fun t ht => ?_
                rw [Set.uIcc_of_le hx] at ht
                have ht2 : (2 : ℝ) ≤ t := ht.1
                have ht0 : (0 : ℝ) < t := by linarith
                have hlt_pos : (0 : ℝ) < Real.log t :=
                  (Real.log_pos (by norm_num)).trans_le (Real.log_le_log (by norm_num) ht2)
                rw [abs_div, abs_of_pos (mul_pos ht0 (by positivity))]


/-! ## Section 5: the per-q master bound -/

/-- For `q ≥ 1` the coprime residue filter is nonempty. -/
theorem coprime_filter_nonempty {q : ℕ} (hq : 0 < q) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).Nonempty := by
  rcases Nat.lt_or_ge q 2 with hq2 | hq2
  · have hq1 : q = 1 := by omega
    subst hq1
    exact ⟨0, by simp⟩
  · exact ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega : 1 < q), by simp⟩⟩

/-- Trivial uniform bound for `psiAPMaxError`. -/
theorem psiAPMaxError_le_class {q : ℕ} (hq : 0 < q) {t : ℝ} (ht : 2 ≤ t) :
    Stage11BombieriVinogradov.psiAPMaxError q t ≤
      (t / (q : ℝ) + 1) * Real.log t + t / ((q.totient : ℕ) : ℝ) := by
  have hne := coprime_filter_nonempty hq
  rw [Stage11BombieriVinogradov.psiAPMaxError, dif_pos hne]
  refine Finset.sup'_le hne
    (fun a => |Stage2DirichletAP.chebyshevPsiAP q a t - t / ((q.totient : ℕ) : ℝ)|) fun a _ => ?_
  rw [abs_le]
  have hlog : (0 : ℝ) ≤ Real.log t := Real.log_nonneg (by linarith : (1 : ℝ) ≤ t)
  have hqpos : (0 : ℝ) ≤ t / (q : ℝ) := div_nonneg (by linarith : (0 : ℝ) ≤ t)
    (by positivity : (0 : ℝ) ≤ (q : ℝ))
  have hφpos : (0 : ℝ) < ((q.totient : ℕ) : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφ1 : (1 : ℝ) ≤ ((q.totient : ℕ) : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφle : t / ((q.totient : ℕ) : ℝ) ≤ t :=
    div_le_self (by linarith : (0 : ℝ) ≤ t) hφ1
  have hφnn : (0 : ℝ) ≤ t / ((q.totient : ℕ) : ℝ) := div_nonneg (by linarith : (0 : ℝ) ≤ t) hφpos.le
  have hψnn : (0 : ℝ) ≤ Stage2DirichletAP.chebyshevPsiAP q a t := by
    have := Stage2DirichletAP.chebyshevThetaAP_nonneg q a t
    have hle := Stage2DirichletAP.chebyshevThetaAP_le_chebyshevPsiAP q a t
    linarith
  constructor
  · have h1 : Stage2DirichletAP.chebyshevPsiAP q a t ≤ (t / (q : ℝ) + 1) * Real.log t :=
      chebyshevPsiAP_le_class hq a ht
    linarith
  · have h1 : (0 : ℝ) ≤ (t / (q : ℝ) + 1) * Real.log t := by positivity
    have h2 : Stage2DirichletAP.chebyshevPsiAP q a t ≤ (t / (q : ℝ) + 1) * Real.log t :=
      chebyshevPsiAP_le_class hq a ht
    linarith

/-- Integrability of the uniform per-q bound integrand. -/
theorem intervalIntegrable_bound_integrand {q : ℕ} (hq : 0 < q) {u v : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) :
    IntervalIntegrable (fun t : ℝ =>
      (Stage11BombieriVinogradov.psiAPMaxError q t + Real.sqrt t * Real.log t +
        (Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) /
          ((q.totient : ℕ) : ℝ)) / (t * (Real.log t) ^ 2)) volume u v := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hφ : (1 : ℝ) ≤ ((q.totient : ℕ) : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mpr ?_
  refine Integrable.mono'
    (integrableOn_const (C := 16 / (Real.log 2) ^ 2) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
  · have hA : Measurable (fun s : ℝ => Stage11BombieriVinogradov.psiAPMaxError q s) :=
      measurable_psiAPMaxError q
    have hB : Measurable (fun s : ℝ => Real.sqrt s * Real.log s) :=
      (Real.continuous_sqrt).measurable.mul Real.measurable_log
    have hC : Measurable (fun s : ℝ => Stage11BombieriVinogradov.psiAPMaxError 1 s) :=
      measurable_psiAPMaxError 1
    have hD : Measurable (fun s : ℝ => s * (Real.log s) ^ 2) :=
      measurable_id.mul (Real.measurable_log.pow_const 2)
    exact (((hA.add hB).add ((hC.add hB).div_const ((q.totient : ℕ) : ℝ))).div
      hD).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
    have ht2 : 2 ≤ t := hu.trans ht.1.le
    have ht0 : (0 : ℝ) < t := by linarith
    have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
    have hlt_pos : (0 : ℝ) < Real.log t := hlog2.trans_le hlt
    have hsq : Real.sqrt t ≤ t := by
      refine Real.sqrt_le_iff.mpr ⟨by positivity, by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ t by linarith)]⟩
    have hpsi1 : Stage11BombieriVinogradov.psiAPMaxError q t ≤
        (t / (q : ℝ) + 1) * Real.log t + t / ((q.totient : ℕ) : ℝ) :=
      psiAPMaxError_le_class hq ht2
    have hpsi2 : Stage11BombieriVinogradov.psiAPMaxError 1 t ≤
        (t + 1) * Real.log t + t := by
      simpa using psiAPMaxError_le_class one_pos ht2
    have hA' : Real.sqrt t * Real.log t ≤ t * Real.log t :=
      mul_le_mul_of_nonneg_right hsq hlt_pos.le
    have h1le : (1 : ℝ) ≤ t := by linarith
    have hone : (1 : ℝ) * Real.log t ≤ t * Real.log t := by
      exact mul_le_mul_of_nonneg_right h1le hlt_pos.le
    have hqle : t / (q : ℝ) ≤ t :=
      div_le_self (by linarith : (0 : ℝ) ≤ t) (by exact_mod_cast (by omega : (1 : ℕ) ≤ q))
    have hφdiv : (Stage11BombieriVinogradov.psiAPMaxError 1 t +
        Real.sqrt t * Real.log t) / ((q.totient : ℕ) : ℝ) ≤
        Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t :=
      div_le_self (by
        exact add_nonneg (Stage11BombieriVinogradov.psiAPMaxError_nonneg 1 t)
          (mul_nonneg (Real.sqrt_nonneg t) (Real.log_nonneg (by linarith : (1 : ℝ) ≤ t)))) hφ
    have hlog2half : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
        rw [← Real.log_exp (1 : ℝ)]
        exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
      have hlog4' : Real.log 4 = 2 * Real.log 2 := by
        have := Real.log_pow (x := (2 : ℝ)) 2
        norm_num at this ⊢
        exact this
      nlinarith
    have htle : t ≤ 2 * t * Real.log t := by nlinarith [hlt, hlog2half, ht0]
    have hφleT : t / ((q.totient : ℕ) : ℝ) ≤ t :=
      div_le_self (by linarith : (0 : ℝ) ≤ t) hφ
    have hnum : Stage11BombieriVinogradov.psiAPMaxError q t + Real.sqrt t * Real.log t +
        (Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) /
          ((q.totient : ℕ) : ℝ) ≤ 12 * t * Real.log t := by
      nlinarith [hpsi1, hpsi2, hA', hone, hqle, hφdiv, htle, hlt_pos, hφleT]
    have hXnn : (0 : ℝ) ≤ Stage11BombieriVinogradov.psiAPMaxError q t +
        Real.sqrt t * Real.log t +
        (Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) /
          ((q.totient : ℕ) : ℝ) := by
      have h1 := Stage11BombieriVinogradov.psiAPMaxError_nonneg q t
      have h2 := Stage11BombieriVinogradov.psiAPMaxError_nonneg 1 t
      have h3 : (0 : ℝ) ≤ Real.sqrt t * Real.log t :=
        mul_nonneg (Real.sqrt_nonneg t) hlt_pos.le
      have h4 : (0 : ℝ) ≤ (Stage11BombieriVinogradov.psiAPMaxError 1 t +
          Real.sqrt t * Real.log t) / ((q.totient : ℕ) : ℝ) :=
        div_nonneg (add_nonneg h2 h3) (by positivity : (0 : ℝ) ≤ ((q.totient : ℕ) : ℝ))
      exact add_nonneg (add_nonneg h1 h3) h4
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hXnn,
      abs_of_pos (mul_pos ht0 (by positivity))]
    calc (Stage11BombieriVinogradov.psiAPMaxError q t + Real.sqrt t * Real.log t +
          (Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) /
            ((q.totient : ℕ) : ℝ)) / (t * (Real.log t) ^ 2)
        ≤ (16 * t * Real.log t) / (t * (Real.log t) ^ 2) :=
            div_le_div_of_nonneg_right (hnum.trans (by nlinarith)) (by positivity)
      _ = 16 / Real.log t := by field_simp [ht0.ne', hlt_pos.ne']
      _ ≤ 16 / (Real.log 2) ^ 2 := by
            have hl2 : Real.log 2 < (7 : ℝ) / 10 := by linarith [Real.log_two_lt_d9]
            refine div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 16)
              (by positivity : (0 : ℝ) < (Real.log 2) ^ 2) ?_
            nlinarith [hlt, hlog2, hl2]


/-- **The per-q master bound**: the sup over units of the `π`-error is bounded by
the `psiAPMaxError`-based expression at `x` plus its integral. -/
theorem unit_bound {q : ℕ} (hq : 0 < q) {x : ℝ} (hx : 2 ≤ x) :
    ⨆ a : (ZMod q)ˣ, |((Real.primeCountingZMod x q (a : ZMod q) : ℕ) : ℝ) -
        _root_.pi x / ((q.totient : ℕ) : ℝ)| ≤
      (Stage11BombieriVinogradov.psiAPMaxError q x + Real.sqrt x * Real.log x +
        (Stage11BombieriVinogradov.psiAPMaxError 1 x + Real.sqrt x * Real.log x) /
          ((q.totient : ℕ) : ℝ)) / Real.log x +
      ∫ t in (2 : ℝ)..x, (Stage11BombieriVinogradov.psiAPMaxError q t +
          Real.sqrt t * Real.log t +
          (Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) /
            ((q.totient : ℕ) : ℝ)) / (t * (Real.log t) ^ 2) := by
  refine ciSup_le fun a => ?_
  have hne : NeZero q := ⟨hq.ne'⟩
  have hcop : Nat.Coprime (ZMod.val (a : ZMod q)) q := unit_val_coprime a
  have hcast : Real.primeCountingZMod x q (a : ZMod q) =
      Stage2DirichletAP.primeCountAP q (ZMod.val (a : ZMod q)) x := by
    have h := primeCountingZMod_eq_primeCountAP (q := q) x (ZMod.val (a : ZMod q))
    rwa [← zmod_eq_val_cast (a : ZMod q)] at h
  have hval : (0 : ℝ) < Real.log x := Real.log_pos (by linarith : (1 : ℝ) < x)
  have hdecompX := abs_thetaAP_sub_theta_div_le hq (ZMod.val (a : ZMod q)) hcop
    (by linarith : (1 : ℝ) ≤ x)
  have hintX : IntervalIntegrable (fun t : ℝ =>
      (Stage2DirichletAP.chebyshevThetaAP q (ZMod.val (a : ZMod q)) t -
        RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)) /
      (t * (Real.log t) ^ 2)) volume (2 : ℝ) x :=
    intervalIntegrable_theta_err hq (ZMod.val (a : ZMod q)) (le_rfl (a := (2 : ℝ))) hx
  have hintB : IntervalIntegrable (fun t : ℝ =>
      (Stage11BombieriVinogradov.psiAPMaxError q t + Real.sqrt t * Real.log t +
        (Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) /
          ((q.totient : ℕ) : ℝ)) / (t * (Real.log t) ^ 2)) volume (2 : ℝ) x :=
    intervalIntegrable_bound_integrand hq (le_rfl (a := (2 : ℝ))) hx
  rw [hcast]
  have habel := abel_diff_le hq (ZMod.val (a : ZMod q)) hx
  calc |((Stage2DirichletAP.primeCountAP q (ZMod.val (a : ZMod q)) x : ℕ) : ℝ) -
        _root_.pi x / ((q.totient : ℕ) : ℝ)|
      ≤ |Stage2DirichletAP.chebyshevThetaAP q (ZMod.val (a : ZMod q)) x -
          RHDirect.Stage2DirichletAP.chebyshevTheta x / ((q.totient : ℕ) : ℝ)| /
          Real.log x +
        (∫ t in (2 : ℝ)..x, |Stage2DirichletAP.chebyshevThetaAP q (ZMod.val (a : ZMod q)) t -
          RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)| /
          (t * (Real.log t) ^ 2)) := habel
    _ ≤ (Stage11BombieriVinogradov.psiAPMaxError q x + Real.sqrt x * Real.log x +
          (Stage11BombieriVinogradov.psiAPMaxError 1 x + Real.sqrt x * Real.log x) /
            ((q.totient : ℕ) : ℝ)) / Real.log x +
        ∫ t in (2 : ℝ)..x, (Stage11BombieriVinogradov.psiAPMaxError q t +
          Real.sqrt t * Real.log t +
          (Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) /
            ((q.totient : ℕ) : ℝ)) / (t * (Real.log t) ^ 2) := by
        refine add_le_add ?_ ?_
        · exact div_le_div_of_nonneg_right hdecompX hval.le
        · have hcong : (∫ t in (2 : ℝ)..x,
                |Stage2DirichletAP.chebyshevThetaAP q (ZMod.val (a : ZMod q)) t -
                  RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)| /
                (t * (Real.log t) ^ 2)) =
              (∫ t in (2 : ℝ)..x,
                |(Stage2DirichletAP.chebyshevThetaAP q (ZMod.val (a : ZMod q)) t -
                  RHDirect.Stage2DirichletAP.chebyshevTheta t / ((q.totient : ℕ) : ℝ)) /
                  (t * (Real.log t) ^ 2)|) :=
              intervalIntegral.integral_congr fun t ht => by
                rw [Set.uIcc_of_le hx] at ht
                have ht2 : (2 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
                have htp : (0 : ℝ) < t := by linarith
                have hlp : (0 : ℝ) < Real.log t :=
                  (Real.log_pos (by norm_num)).trans_le (Real.log_le_log (by norm_num) ht2)
                rw [abs_div, abs_of_pos (mul_pos htp (sq_pos_of_pos hlp))]
          rw [hcong]
          refine intervalIntegral.integral_mono_on hx hintX.abs hintB fun t ht => ?_
          have ht2 : (2 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
          have hdecompT := abs_thetaAP_sub_theta_div_le hq (ZMod.val (a : ZMod q)) hcop
            (by linarith : (1 : ℝ) ≤ t)
          have htp : (0 : ℝ) < t := by linarith
          have hlp : (0 : ℝ) < Real.log t :=
            (Real.log_pos (by norm_num)).trans_le (Real.log_le_log (by norm_num) ht2)
          rw [abs_div, abs_of_pos (mul_pos htp (sq_pos_of_pos hlp))]
          exact div_le_div_of_nonneg_right hdecompT (by positivity)


/-- Elementary lower bound `1/2 ≤ log 2`. -/
private theorem half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hlog4' : Real.log 4 = 2 * Real.log 2 := by
    have := Real.log_pow (x := (2 : ℝ)) 2
    norm_num at this ⊢
    exact this
  nlinarith

/-- Elementary integral bound: `∫₂ᵀ (1 / t) dt ≤ log T` for `T ≥ 2`. -/
private theorem integral_one_div_le {T : ℝ} (hT : 2 ≤ T) :
    ∫ t in (2 : ℝ)..T, (1 / t) ≤ Real.log T := by
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) T, HasDerivAt Real.log (1 / t) t := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have htpos : (0 : ℝ) < t := by linarith [ht.1]
    simpa [one_div] using Real.hasDerivAt_log htpos.ne'
  have hint : IntervalIntegrable (fun t : ℝ => 1 / t) volume (2 : ℝ) T := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hT]
    exact continuousOn_const.div continuousOn_id fun t ht => by linarith [ht.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

/-- Elementary integral bound: `∫₂ᵀ (1 / √t) dt ≤ 2√T` for `T ≥ 2`. -/
private theorem integral_one_div_sqrt_le {T : ℝ} (hT : 2 ≤ T) :
    ∫ t in (2 : ℝ)..T, (1 / Real.sqrt t) ≤ 2 * Real.sqrt T := by
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) T,
      HasDerivAt (fun s : ℝ => 2 * Real.sqrt s) (1 / Real.sqrt t) t := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have htpos : (0 : ℝ) < t := by linarith [ht.1]
    have hsq : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr htpos
    have h1 := (Real.hasDerivAt_sqrt htpos.ne').const_mul (2 : ℝ)
    refine h1.congr_deriv ?_
    field_simp [hsq.ne']
  have hint : IntervalIntegrable (fun t : ℝ => 1 / Real.sqrt t) volume (2 : ℝ) T := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hT]
    exact continuousOn_const.div Real.continuous_sqrt.continuousOn fun t ht =>
      (Real.sqrt_pos.mpr (by linarith [ht.1])).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hsq2 : (0 : ℝ) ≤ 2 * Real.sqrt 2 := by positivity
  linarith

/-- Level geometry: for `t ≥ max(t₀, x^β)` with `log^{2Bv} t ≤ t^{η/8}` and `2θ ≤ β(1 - η/8)`,
every modulus `q ≤ ⌊x^θ⌋₊` lies inside the Bombieri–Vinogradov range `⌊√t / log^{Bv} t⌋₊`. -/
private theorem floor_rpow_le_bv_level {θ η β Bv x t : ℝ}
    (hθpos : 0 < θ) (hηdef : η = 1 / 2 - θ) (hβkey : 2 * θ ≤ β * (1 - η / 8))
    (hx : 3 ≤ x) (ht3 : 3 ≤ t) (hxt : x ^ β ≤ t)
    (hlogt : (Real.log t) ^ (2 * Bv) ≤ t ^ (η / 8)) :
    ⌊x ^ θ⌋₊ ≤ ⌊Real.sqrt t / (Real.log t) ^ Bv⌋₊ := by
  refine Nat.floor_mono ?_
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hlt_pos : (0 : ℝ) < Real.log t := Real.log_pos (by linarith : (1 : ℝ) < t)
  have hlb_pos : (0 : ℝ) < (Real.log t) ^ Bv := rpow_pos_of_pos hlt_pos Bv
  rw [le_div_iff₀ hlb_pos]
  have h1_sub_nn : (0 : ℝ) ≤ 1 - η / 8 := by linarith
  have hxθ_nn : (0 : ℝ) ≤ x ^ θ := rpow_nonneg (by linarith : (0 : ℝ) ≤ x) θ
  have hprod_nn : (0 : ℝ) ≤ x ^ θ * (Real.log t) ^ Bv := mul_nonneg hxθ_nn hlb_pos.le
  have hsq_lhs : (x ^ θ * (Real.log t) ^ Bv) ^ 2 = x ^ (2 * θ) * (Real.log t) ^ (2 * Bv) := by
    rw [mul_pow, ← rpow_natCast (x ^ θ) 2, ← rpow_natCast ((Real.log t) ^ Bv) 2,
      ← rpow_mul (by linarith : (0 : ℝ) ≤ x), ← rpow_mul hlt_pos.le]
    push_cast
    ring_nf
  have hstep1 : x ^ (2 * θ) ≤ t ^ (1 - η / 8) := by
    calc x ^ (2 * θ)
        ≤ x ^ (β * (1 - η / 8)) := rpow_le_rpow_of_exponent_le hx1 hβkey
      _ = (x ^ β) ^ (1 - η / 8) := rpow_mul (by linarith : (0 : ℝ) ≤ x) β (1 - η / 8)
      _ ≤ t ^ (1 - η / 8) :=
          rpow_le_rpow (rpow_nonneg (by linarith : (0 : ℝ) ≤ x) β) hxt h1_sub_nn
  have hsq_le : (x ^ θ * (Real.log t) ^ Bv) ^ 2 ≤ (Real.sqrt t) ^ 2 := by
    rw [hsq_lhs, Real.sq_sqrt ht0.le]
    calc x ^ (2 * θ) * (Real.log t) ^ (2 * Bv)
        ≤ t ^ (1 - η / 8) * t ^ (η / 8) :=
          mul_le_mul hstep1 hlogt (rpow_nonneg hlt_pos.le _) (rpow_nonneg ht0.le _)
      _ = t ^ ((1 - η / 8) + η / 8) := (rpow_add ht0 _ _).symm
      _ = t := by ring_nf; exact rpow_one t
  nlinarith [Real.sqrt_nonneg t, hprod_nn, hsq_le]

/-- Eventually any constant is beaten by `x ^ r` for `r > 0`. -/
theorem eventually_const_le_rpow (K r : ℝ) (hr : 0 < r) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |K| ≤ x ^ r := by
  have hK1 : (0 : ℝ) < |K| + 1 := by positivity
  refine ⟨(|K| + 1) ^ (1 / r), fun x hx => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := le_trans (rpow_nonneg hK1.le _) hx
  have hmono : ((|K| + 1) ^ (1 / r)) ^ r ≤ x ^ r :=
    Real.rpow_le_rpow (rpow_nonneg hK1.le _) hx hr.le
  rw [← Real.rpow_mul hK1.le (1 / r) r, one_div_mul_cancel hr.ne',
    Real.rpow_one] at hmono
  have : |K| ≤ |K| + 1 := by linarith
  linarith [this, hmono]

/-- **The Maynard–Tao Bombieri–Vinogradov theorem, unconditional**:
`PrimeGapsTheory.BombieriVinogradov` follows from `RHDirect`'s unconditional
Bombieri–Vinogradov theorem. -/
theorem maynardBombieriVinogradov : BombieriVinogradov := by
  intro θ hθ A hA
  by_cases hθ0 : θ ≤ 0
  · -- `θ ≤ 0`: trivial, `c := 1`
    refine ⟨1, one_pos, fun x hx3 => ?_⟩
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hle0 : x ^ θ ≤ x ^ (0 : ℝ) := rpow_le_rpow_of_exponent_le hx1 hθ0
    have hle1 : x ^ θ ≤ ((1 : ℕ) : ℝ) := by
      rw [rpow_zero] at hle0
      rw [Nat.cast_one]
      exact hle0
    have hnn : (0 : ℝ) ≤ x ^ θ := rpow_nonneg (by linarith : (0 : ℝ) ≤ x) θ
    have hQc : ((⌊x ^ θ⌋₊ : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) := le_trans (Nat.floor_le hnn) hle1
    have hQ : ⌊x ^ θ⌋₊ ≤ 1 := Nat.cast_le.mp hQc
    rcases Nat.lt_or_ge ⌊x ^ θ⌋₊ 1 with hQ0 | hQ1
    · rw [show ⌊x ^ θ⌋₊ = 0 from by omega, Finset.Icc_eq_empty (by omega),
        Finset.sum_empty]
      have hxp : (0 : ℝ) < x := by linarith
      have hxpos : (0 : ℝ) < x ^ A := rpow_pos_of_pos hxp A
      have hlx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
      exact div_nonneg (mul_nonneg zero_le_one (by linarith : (0 : ℝ) ≤ x))
        (rpow_nonneg hlx A)
    · rw [show ⌊x ^ θ⌋₊ = 1 from by omega, Finset.Icc_self, Finset.sum_singleton]
      have hz : ∀ a : (ZMod 1)ˣ, |((Real.primeCountingZMod x 1 (a : ZMod 1) : ℕ) : ℝ) -
          _root_.pi x / ((Nat.totient 1 : ℕ) : ℝ)| = 0 := by
        intro a
        rw [Real.primeCountingZMod_one_eq_primeCounting, Nat.totient_one]
        simp
      refine ciSup_le fun a => ?_
      rw [hz a]
      have hlx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith : (1 : ℝ) < x)
      have : (0 : ℝ) < x ^ A := rpow_pos_of_pos (x := x) (by linarith : (0 : ℝ) < x) A
      positivity
  · -- `0 < θ < 1/2`: the main case
    have hθpos : (0 : ℝ) < θ := by linarith
    have hθhalf : θ < 1 / 2 := hθ
    -- Bombieri–Vinogradov at level `A + 8`
    obtain ⟨Bv, Cv, hBv, hCv, hBV⟩ :=
      RHDirect.Stage11BombieriVinogradov.bombieri_vinogradov (A + 8)
    -- the level-geometry constants
    set η : ℝ := 1 / 2 - θ with hηdef
    have hηpos : (0 : ℝ) < η := by rw [hηdef]; linarith
    have hη8 : (0 : ℝ) < η / 8 := by linarith
    set β : ℝ := (1 + 2 * θ) / 2 with hβdef
    have hβhalf : (1 : ℝ) / 2 ≤ β := by rw [hβdef]; linarith
    have hβone : β ≤ 1 := by rw [hβdef]; linarith
    -- key algebraic fact: `2θ ≤ β·(1 - η/8)` (so the level covers all moduli)
    have hβkey : 2 * θ ≤ β * (1 - η / 8) := by
      rw [hηdef, hβdef]
      field_simp
      have hpow : (0 : ℝ) ≤ (θ - 1 / 2) * (θ - 15 / 2) := by nlinarith
      nlinarith
    -- absolute threshold `t₀`: `log^{2Bv} t ≤ t^{η/8}` for `t ≥ t₀`
    obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp
      (eventually_log_pow_le_rpow (C := 2 * Bv) (r := η / 8) hη8)
    set t₀ : ℝ := max 3 T₀ with ht₀def
    have ht₀3 : (3 : ℝ) ≤ t₀ := le_max_left _ _
    have ht₀T : ∀ t : ℝ, t₀ ≤ t → (Real.log t) ^ (2 * Bv) ≤ t ^ (η / 8) := fun t ht =>
      hT₀ t (le_trans (le_max_right _ _) ht)
    -- the master eventual log bound
    obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp
      (eventually_log_pow_le_rpow (C := A + 2 * Bv + 40) (r := η / 2)
        (by linarith : (0 : ℝ) < η / 2))
    -- constants beat powers, eventually
    obtain ⟨X₂, hX₂⟩ := eventually_const_le_rpow 1 (η / 4) (by linarith : (0 : ℝ) < η / 4)
    obtain ⟨X₃, hX₃⟩ := eventually_const_le_rpow 1 ((1 - η) / 4)
      (by linarith : (0 : ℝ) < (1 - η) / 4)
    set X₀ : ℝ := max 3 (max t₀ (max (t₀ * t₀) (max (Real.exp 1) (max X₁ (max X₂ X₃)))))
      with hX₀def
    have hX₀3 : (3 : ℝ) ≤ X₀ := by dsimp only [hX₀def, X₀]; simp
    have hX₀t₀ : t₀ ≤ X₀ := by dsimp only [hX₀def, X₀]; simp
    have hX₀t₀sq : t₀ * t₀ ≤ X₀ := by
      dsimp only [hX₀def, X₀]
      exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    have hX₀e : Real.exp 1 ≤ X₀ := by dsimp only [hX₀def, X₀]; simp
    have hX₀X₁ : X₁ ≤ X₀ := by
      dsimp only [hX₀def, X₀]
      exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
    have hX₀pos : (0 : ℝ) < X₀ := by linarith
    -- the eventual asymptotic bound
    have hasym : ∃ K : ℝ, (1 : ℝ) ≤ K ∧ ∀ x : ℝ, X₀ ≤ x →
        ∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊,
            ⨆ a : (ZMod q)ˣ, |((Real.primeCountingZMod x q (a : ZMod q) : ℕ) : ℝ) -
              _root_.pi x / ((q.totient : ℕ) : ℝ)| ≤
          K * x / (Real.log x) ^ A := by
      set K : ℝ := 13 * Cv + 25 * Cv * (2 : ℝ) ^ A + 216 with hKdef
      have h2A_pos : (0 : ℝ) < (2 : ℝ) ^ A := rpow_pos_of_pos (by norm_num) A
      have hK1 : (1 : ℝ) ≤ K := by rw [hKdef]; nlinarith [hCv, h2A_pos]
      refine ⟨K, hK1, fun x hxX => ?_⟩
      have hx3 : (3 : ℝ) ≤ x := le_trans hX₀3 hxX
      have hx2 : (2 : ℝ) ≤ x := by linarith
      have hx1 : (1 : ℝ) ≤ x := by linarith
      have hx0 : (0 : ℝ) < x := by linarith
      have hxe : Real.exp 1 ≤ x := le_trans hX₀e hxX
      have hlogx1 : (1 : ℝ) ≤ Real.log x := by
        have h := Real.log_le_log (Real.exp_pos 1) hxe
        rwa [Real.log_exp (1 : ℝ)] at h
      have hlogx_pos : (0 : ℝ) < Real.log x := by linarith
      have hlogA_pos : (0 : ℝ) < (Real.log x) ^ A := rpow_pos_of_pos hlogx_pos A
      have hxX₁ : (Real.log x) ^ (A + 2 * Bv + 40) ≤ x ^ (η / 2) :=
        hX₁ x (le_trans hX₀X₁ hxX)
      have hlogA_le_xη2 : (Real.log x) ^ A ≤ x ^ (η / 2) := by
        have h1 : (Real.log x) ^ A ≤ (Real.log x) ^ (A + 2 * Bv + 40) :=
          rpow_le_rpow_of_exponent_le hlogx1 (by linarith)
        exact le_trans h1 hxX₁
      have hlogA1_le_xη : (Real.log x) ^ (A + 1) ≤ x ^ η := by
        have h1 : (Real.log x) ^ (A + 1) ≤ (Real.log x) ^ (A + 2 * Bv + 40) :=
          rpow_le_rpow_of_exponent_le hlogx1 (by linarith)
        have h2 : x ^ (η / 2) ≤ x ^ η := rpow_le_rpow_of_exponent_le hx1 (by linarith)
        exact le_trans (le_trans h1 hxX₁) h2
      have hlogA_le_xη : (Real.log x) ^ A ≤ x ^ η := by
        have h2 : x ^ (η / 2) ≤ x ^ η := rpow_le_rpow_of_exponent_le hx1 (by linarith)
        exact le_trans hlogA_le_xη2 h2
      have hx1η_log_le : x ^ (1 - η) * Real.log x ≤ x / (Real.log x) ^ A := by
        rw [le_div_iff₀ hlogA_pos]
        have hlogprod : Real.log x * (Real.log x) ^ A = (Real.log x) ^ (A + 1) := by
          rw [mul_comm, rpow_add hlogx_pos, rpow_one]
        have hxprod : x ^ (1 - η) * x ^ η = x := by
          rw [← rpow_add hx0]; ring_nf; exact rpow_one x
        calc x ^ (1 - η) * Real.log x * (Real.log x) ^ A
            = x ^ (1 - η) * (Real.log x * (Real.log x) ^ A) := by ring
          _ = x ^ (1 - η) * (Real.log x) ^ (A + 1) := by rw [hlogprod]
          _ ≤ x ^ (1 - η) * x ^ η :=
              mul_le_mul_of_nonneg_left hlogA1_le_xη (rpow_nonneg hx0.le _)
          _ = x := hxprod
      have hx1η_le : x ^ (1 - η) ≤ x / (Real.log x) ^ A := by
        have h1 : x ^ (1 - η) ≤ x ^ (1 - η) * Real.log x :=
          le_mul_of_one_le_right (rpow_nonneg hx0.le _) hlogx1
        exact le_trans h1 hx1η_log_le
      -- Modulus count `Q := ⌊x^θ⌋₊` and reciprocal sums
      set Q : ℕ := ⌊x ^ θ⌋₊ with hQdef
      have hQ1 : 1 ≤ Q := by
        rw [hQdef]
        refine (Nat.one_le_floor_iff (x := x ^ θ)).mpr ?_
        calc (1 : ℝ) = (1 : ℝ) ^ θ := (one_rpow θ).symm
          _ ≤ x ^ θ := rpow_le_rpow (by norm_num) hx1 hθpos.le
      have hQ_le_xθ : (Q : ℝ) ≤ x ^ θ := Nat.floor_le (rpow_nonneg hx0.le θ)
      have hQ_le_x : (Q : ℝ) ≤ x := by
        refine le_trans hQ_le_xθ ?_
        calc x ^ θ ≤ x ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hx1 (by linarith)
          _ = x := rpow_one x
      have hharm : ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ))⁻¹ ≤ 2 * Real.log x := by
        have h1 := Stage5DirichletLZeroFree.harmonic_sum_le_log_add_one hQ1
        have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ1
        have hlogQ : Real.log (Q : ℝ) ≤ Real.log x := Real.log_le_log hQpos hQ_le_x
        linarith
      have htot : ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ ≤ 12 * Real.log x := by
        have h1 := Stage8BarbanDavenport.sum_inv_totient_le_log hQ1
        have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ1
        have h2Q : 2 * (Q : ℝ) ≤ x ^ (2 : ℕ) := by nlinarith [hQ_le_x, hx3]
        have hlog2Q : Real.log (2 * (Q : ℝ)) ≤ 2 * Real.log x := by
          have h := Real.log_le_log (by positivity) h2Q
          rwa [Real.log_pow, Nat.cast_ofNat] at h
        linarith
      -- Split point `T := x ^ β` with `2 ≤ 3 ≤ t₀ ≤ T ≤ x`
      set T : ℝ := x ^ β with hTdef
      have hβ_eq : β = 1 - η := by rw [hβdef, hηdef]; ring
      have hT_eq : T = x ^ (1 - η) := by rw [hTdef, hβ_eq]
      have ht₀_le_T : t₀ ≤ T := by
        have hsq : t₀ * t₀ ≤ x := le_trans hX₀t₀sq hxX
        have ht₀_le_sqrt : t₀ ≤ Real.sqrt x := by
          rw [Real.le_sqrt (by linarith) hx0.le]
          linarith
        have hsqrt_le : Real.sqrt x ≤ x ^ β := by
          rw [Real.sqrt_eq_rpow]
          exact rpow_le_rpow_of_exponent_le hx1 hβhalf
        exact le_trans ht₀_le_sqrt hsqrt_le
      have hT3 : (3 : ℝ) ≤ T := le_trans ht₀3 ht₀_le_T
      have hT2 : (2 : ℝ) ≤ T := by linarith
      have hTx : T ≤ x := by
        calc T = x ^ β := rfl
          _ ≤ x ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hx1 hβone
          _ = x := rpow_one x
      -- Uniform bound integrand `F q t`
      let F : ℕ → ℝ → ℝ := fun q t =>
        (Stage11BombieriVinogradov.psiAPMaxError q t + Real.sqrt t * Real.log t +
          (Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) /
            ((q.totient : ℕ) : ℝ)) / (t * (Real.log t) ^ 2)
      have hintSum : ∀ {u v : ℝ}, 2 ≤ u → u ≤ v →
          IntervalIntegrable (fun t => ∑ q ∈ Finset.Icc 1 Q, F q t) volume u v := by
        intro u v hu huv
        have heq : (fun t => ∑ q ∈ Finset.Icc 1 Q, F q t) = ∑ q ∈ Finset.Icc 1 Q, F q := by
          funext t
          exact (Finset.sum_apply t (Finset.Icc 1 Q) F).symm
        rw [heq]
        exact IntervalIntegrable.sum (Finset.Icc 1 Q) fun q hq =>
          intervalIntegrable_bound_integrand (Finset.mem_Icc.mp hq).1 hu huv
      -- Step 1: apply `unit_bound` to every `q ∈ Icc 1 Q` and commute `∑` and `∫`
      have hsum_ub : ∑ q ∈ Finset.Icc 1 Q,
            ⨆ a : (ZMod q)ˣ, |((Real.primeCountingZMod x q (a : ZMod q) : ℕ) : ℝ) -
              _root_.pi x / ((q.totient : ℕ) : ℝ)| ≤
          (∑ q ∈ Finset.Icc 1 Q,
            (Stage11BombieriVinogradov.psiAPMaxError q x + Real.sqrt x * Real.log x +
              (Stage11BombieriVinogradov.psiAPMaxError 1 x + Real.sqrt x * Real.log x) /
                ((q.totient : ℕ) : ℝ)) / Real.log x) +
          (∫ t in (2 : ℝ)..T, ∑ q ∈ Finset.Icc 1 Q, F q t) +
          (∫ t in T..x, ∑ q ∈ Finset.Icc 1 Q, F q t) := by
        have h1 : ∑ q ∈ Finset.Icc 1 Q,
              ⨆ a : (ZMod q)ˣ, |((Real.primeCountingZMod x q (a : ZMod q) : ℕ) : ℝ) -
                _root_.pi x / ((q.totient : ℕ) : ℝ)| ≤
            ∑ q ∈ Finset.Icc 1 Q,
              ((Stage11BombieriVinogradov.psiAPMaxError q x + Real.sqrt x * Real.log x +
                (Stage11BombieriVinogradov.psiAPMaxError 1 x + Real.sqrt x * Real.log x) /
                  ((q.totient : ℕ) : ℝ)) / Real.log x +
                ∫ t in (2 : ℝ)..x, F q t) :=
          Finset.sum_le_sum fun q hq => unit_bound (Finset.mem_Icc.mp hq).1 hx2
        rw [Finset.sum_add_distrib] at h1
        have hcomm : ∑ q ∈ Finset.Icc 1 Q, ∫ t in (2 : ℝ)..x, F q t =
            ∫ t in (2 : ℝ)..x, ∑ q ∈ Finset.Icc 1 Q, F q t :=
          (intervalIntegral.integral_finsetSum fun q hq =>
            intervalIntegrable_bound_integrand (Finset.mem_Icc.mp hq).1 le_rfl hx2).symm
        have hsplit : ∫ t in (2 : ℝ)..x, ∑ q ∈ Finset.Icc 1 Q, F q t =
            (∫ t in (2 : ℝ)..T, ∑ q ∈ Finset.Icc 1 Q, F q t) +
            (∫ t in T..x, ∑ q ∈ Finset.Icc 1 Q, F q t) :=
          (intervalIntegral.integral_add_adjacent_intervals (hintSum le_rfl hT2)
            (hintSum hT2 hTx)).symm
        rw [hcomm, hsplit] at h1
        linarith
      -- Helper: BV bound for `∑_{q ≤ Q} psiAPMaxError q t` whenever `T ≤ t`
      have hBV_on : ∀ t : ℝ, T ≤ t →
          ∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t ≤
            Cv * t / (Real.log t) ^ (A + 8) := by
        intro t htT
        have ht3 : (3 : ℝ) ≤ t := le_trans hT3 htT
        have ht_t₀ : t₀ ≤ t := le_trans ht₀_le_T htT
        have hQle : Q ≤ ⌊Real.sqrt t / (Real.log t) ^ Bv⌋₊ :=
          floor_rpow_le_bv_level hθpos hηdef hβkey hx3 ht3 htT (ht₀T t ht_t₀)
        calc ∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t
            ≤ ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt t / (Real.log t) ^ Bv⌋₊,
                Stage11BombieriVinogradov.psiAPMaxError q t :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hQle)
                fun q _ _ => Stage11BombieriVinogradov.psiAPMaxError_nonneg q t
          _ ≤ Cv * t / (Real.log t) ^ (A + 8) := hBV t ht3
      have hBV1_on : ∀ t : ℝ, T ≤ t →
          Stage11BombieriVinogradov.psiAPMaxError 1 t ≤ Cv * t / (Real.log t) ^ (A + 8) := by
        intro t htT
        calc Stage11BombieriVinogradov.psiAPMaxError 1 t
            ≤ ∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t :=
              Finset.single_le_sum (fun q _ => Stage11BombieriVinogradov.psiAPMaxError_nonneg q t)
                (Finset.mem_Icc.mpr ⟨le_rfl, hQ1⟩)
          _ ≤ Cv * t / (Real.log t) ^ (A + 8) := hBV_on t htT
      -- Step 2: Boundary term at `x`
      have hPiece1 : ∑ q ∈ Finset.Icc 1 Q,
            (Stage11BombieriVinogradov.psiAPMaxError q x + Real.sqrt x * Real.log x +
              (Stage11BombieriVinogradov.psiAPMaxError 1 x + Real.sqrt x * Real.log x) /
                ((q.totient : ℕ) : ℝ)) / Real.log x ≤
          (13 * Cv + 13) * x / (Real.log x) ^ A := by
        have hrew : ∑ q ∈ Finset.Icc 1 Q,
              (Stage11BombieriVinogradov.psiAPMaxError q x + Real.sqrt x * Real.log x +
                (Stage11BombieriVinogradov.psiAPMaxError 1 x + Real.sqrt x * Real.log x) /
                  ((q.totient : ℕ) : ℝ)) / Real.log x =
            (∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q x) / Real.log x +
            (Q : ℝ) * Real.sqrt x +
            ((Stage11BombieriVinogradov.psiAPMaxError 1 x + Real.sqrt x * Real.log x) /
              Real.log x) * ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ := by
          have hcard : ((Finset.Icc 1 Q).card : ℝ) = (Q : ℝ) := by
            have h := Nat.card_Icc 1 Q; exact_mod_cast (by omega : (Finset.Icc 1 Q).card = Q)
          simp_rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
            hcard, div_eq_mul_inv, ← Finset.mul_sum]
          field_simp [hlogx_pos.ne']
        rw [hrew]
        have hlogA8 : (Real.log x) ^ A ≤ (Real.log x) ^ (A + 8) :=
          rpow_le_rpow_of_exponent_le hlogx1 (by linarith)
        have hBVx : ∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q x ≤
            Cv * x / (Real.log x) ^ A := by
          refine le_trans (hBV_on x hTx) ?_
          exact div_le_div_of_nonneg_left (by positivity) hlogA_pos hlogA8
        have h1a : (∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q x) /
              Real.log x ≤ Cv * x / (Real.log x) ^ A :=
          le_trans (div_le_self (Finset.sum_nonneg fun q _ =>
            Stage11BombieriVinogradov.psiAPMaxError_nonneg q x) hlogx1) hBVx
        have h1b : (Q : ℝ) * Real.sqrt x ≤ x / (Real.log x) ^ A := by
          have hmul : (Q : ℝ) * Real.sqrt x ≤ x ^ (1 - η) := by
            rw [Real.sqrt_eq_rpow]
            calc (Q : ℝ) * x ^ (1 / 2 : ℝ)
                ≤ x ^ θ * x ^ (1 / 2 : ℝ) :=
                  mul_le_mul_of_nonneg_right hQ_le_xθ (rpow_nonneg hx0.le _)
              _ = x ^ (θ + 1 / 2) := (rpow_add hx0 _ _).symm
              _ = x ^ (1 - η) := by congr 1; rw [hηdef]; ring
          exact le_trans hmul hx1η_le
        have h1c : ((Stage11BombieriVinogradov.psiAPMaxError 1 x + Real.sqrt x * Real.log x) /
              Real.log x) * ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ ≤
            (12 * Cv + 12) * x / (Real.log x) ^ A := by
          have hpsi1x : Stage11BombieriVinogradov.psiAPMaxError 1 x ≤
              Cv * x / (Real.log x) ^ A := by
            refine le_trans (hBV1_on x hTx) ?_
            exact div_le_div_of_nonneg_left (by positivity) hlogA_pos hlogA8
          have hsqx : Real.sqrt x * Real.log x ≤ x / (Real.log x) ^ A := by
            have hsq_le : Real.sqrt x ≤ x ^ (1 - η) := by
              rw [Real.sqrt_eq_rpow]
              exact rpow_le_rpow_of_exponent_le hx1 (by rw [hηdef]; linarith)
            exact le_trans (mul_le_mul_of_nonneg_right hsq_le hlogx_pos.le) hx1η_log_le
          have hnum_nn : (0 : ℝ) ≤ (Stage11BombieriVinogradov.psiAPMaxError 1 x +
              Real.sqrt x * Real.log x) / Real.log x :=
            div_nonneg (add_nonneg (Stage11BombieriVinogradov.psiAPMaxError_nonneg 1 x)
              (mul_nonneg (Real.sqrt_nonneg x) hlogx_pos.le)) hlogx_pos.le
          calc ((Stage11BombieriVinogradov.psiAPMaxError 1 x + Real.sqrt x * Real.log x) /
                Real.log x) * ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹
              ≤ ((Stage11BombieriVinogradov.psiAPMaxError 1 x + Real.sqrt x * Real.log x) /
                  Real.log x) * (12 * Real.log x) :=
                mul_le_mul_of_nonneg_left htot hnum_nn
            _ = 12 * (Stage11BombieriVinogradov.psiAPMaxError 1 x + Real.sqrt x * Real.log x) := by
                field_simp [hlogx_pos.ne']
            _ ≤ 12 * (Cv * x / (Real.log x) ^ A + x / (Real.log x) ^ A) :=
                mul_le_mul_of_nonneg_left (add_le_add hpsi1x hsqx) (by norm_num)
            _ = (12 * Cv + 12) * x / (Real.log x) ^ A := by ring
        calc (∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q x) / Real.log x +
              (Q : ℝ) * Real.sqrt x +
              ((Stage11BombieriVinogradov.psiAPMaxError 1 x + Real.sqrt x * Real.log x) /
                Real.log x) * ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹
            ≤ Cv * x / (Real.log x) ^ A + x / (Real.log x) ^ A +
              (12 * Cv + 12) * x / (Real.log x) ^ A :=
              add_le_add (add_le_add h1a h1b) h1c
          _ = (13 * Cv + 13) * x / (Real.log x) ^ A := by ring
      -- Step 3: Upper integral `∫_T^x ∑_{q=1}^Q F q t dt`
      have hPiece2 : ∫ t in T..x, ∑ q ∈ Finset.Icc 1 Q, F q t ≤
          (25 * Cv * (2 : ℝ) ^ A + 25) * x / (Real.log x) ^ A := by
        set M : ℝ := (25 * Cv * (2 : ℝ) ^ A + 25) / (Real.log x) ^ A with hMdef
        have hmono : ∫ t in T..x, ∑ q ∈ Finset.Icc 1 Q, F q t ≤ ∫ _t in T..x, M := by
          refine intervalIntegral.integral_mono_on hTx (hintSum hT2 hTx)
            intervalIntegrable_const fun t ht => ?_
          have htT : T ≤ t := ht.1
          have ht3 : (3 : ℝ) ≤ t := le_trans hT3 htT
          have ht0 : (0 : ℝ) < t := by linarith
          have hlogt1 : (1 : ℝ) ≤ Real.log t := by
            have h := Real.log_le_log (Real.exp_pos 1)
              (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ t)
            rwa [Real.log_exp (1 : ℝ)] at h
          have hlogt_pos : (0 : ℝ) < Real.log t := by linarith
          have hlogt_ge : Real.log x / 2 ≤ Real.log t := by
            have h1 : Real.log T ≤ Real.log t := Real.log_le_log (by linarith) htT
            have h2 : Real.log T = β * Real.log x := by rw [hTdef, Real.log_rpow hx0]
            nlinarith [h1, h2, hβhalf, hlogx_pos]
          have hlogtA_ge : (Real.log x) ^ A / (2 : ℝ) ^ A ≤ (Real.log t) ^ A := by
            rw [← div_rpow hlogx_pos.le (by norm_num : (0 : ℝ) ≤ 2)]
            exact rpow_le_rpow (by positivity) hlogt_ge (by linarith)
          have hinv_logtA : 1 / (Real.log t) ^ A ≤ (2 : ℝ) ^ A / (Real.log x) ^ A := by
            rw [div_le_div_iff₀ (rpow_pos_of_pos hlogt_pos A) hlogA_pos]
            have hmul := mul_le_mul_of_nonneg_right hlogtA_ge h2A_pos.le
            have hcancel : (Real.log x) ^ A / (2 : ℝ) ^ A * (2 : ℝ) ^ A = (Real.log x) ^ A :=
              div_mul_cancel₀ _ h2A_pos.ne'
            linarith
          have hsqrtT_le : x ^ (β / 2) ≤ Real.sqrt t := by
            rw [Real.sqrt_eq_rpow]
            calc x ^ (β / 2) = (x ^ β) ^ (1 / 2 : ℝ) := by
                  rw [← rpow_mul hx0.le]; congr 1; ring
              _ ≤ t ^ (1 / 2 : ℝ) := rpow_le_rpow (rpow_nonneg hx0.le β) htT (by norm_num)
          have hrew : ∑ q ∈ Finset.Icc 1 Q, F q t =
              (∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t) /
                (t * (Real.log t) ^ 2) +
              (Q : ℝ) / (Real.sqrt t * Real.log t) +
              (Stage11BombieriVinogradov.psiAPMaxError 1 t / (t * (Real.log t) ^ 2)) *
                (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) +
              (1 / (Real.sqrt t * Real.log t)) *
                (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) := by
            have hcard : ((Finset.Icc 1 Q).card : ℝ) = (Q : ℝ) := by
              have h := Nat.card_Icc 1 Q; exact_mod_cast (by omega : (Finset.Icc 1 Q).card = Q)
            have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
            have hsq_pos : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
            have hsq_div : Real.sqrt t * Real.log t / (t * (Real.log t) ^ 2) =
                1 / (Real.sqrt t * Real.log t) := by
              rw [div_eq_div_iff (by positivity) (by positivity)]
              calc Real.sqrt t * Real.log t * (Real.sqrt t * Real.log t)
                  = (Real.sqrt t * Real.sqrt t) * (Real.log t) ^ 2 := by ring
                _ = 1 * (t * (Real.log t) ^ 2) := by rw [hsq]; ring
            dsimp only [F]
            simp_rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
              hcard, div_eq_mul_inv, ← Finset.mul_sum]
            rw [show ((∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t) +
                  (Q : ℝ) * (Real.sqrt t * Real.log t) +
                  (Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) *
                    ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) * (t * (Real.log t) ^ 2)⁻¹ =
                (∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t) *
                  (t * (Real.log t) ^ 2)⁻¹ +
                (Q : ℝ) * (Real.sqrt t * Real.log t / (t * (Real.log t) ^ 2)) +
                (Stage11BombieriVinogradov.psiAPMaxError 1 t * (t * (Real.log t) ^ 2)⁻¹) *
                  (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) +
                (Real.sqrt t * Real.log t / (t * (Real.log t) ^ 2)) *
                  (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) by ring,
              hsq_div]
            ring
          rw [hrew]
          have h2a : (∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t) /
                (t * (Real.log t) ^ 2) ≤ Cv * (2 : ℝ) ^ A / (Real.log x) ^ A := by
            have hbv := hBV_on t htT
            have hlogA10 : (Real.log t) ^ A ≤ (Real.log t) ^ (A + 8) * (Real.log t) ^ 2 := by
              calc (Real.log t) ^ A ≤ (Real.log t) ^ (A + 8) :=
                    rpow_le_rpow_of_exponent_le hlogt1 (by linarith)
                _ ≤ (Real.log t) ^ (A + 8) * (Real.log t) ^ 2 :=
                    le_mul_of_one_le_right (rpow_nonneg hlogt_pos.le _) (by nlinarith)
            calc (∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t) /
                  (t * (Real.log t) ^ 2)
                ≤ (Cv * t / (Real.log t) ^ (A + 8)) / (t * (Real.log t) ^ 2) :=
                  div_le_div_of_nonneg_right hbv (by positivity)
              _ = Cv / ((Real.log t) ^ (A + 8) * (Real.log t) ^ 2) := by
                  field_simp [ht0.ne', (rpow_pos_of_pos hlogt_pos (A + 8)).ne', hlogt_pos.ne']
              _ ≤ Cv / (Real.log t) ^ A :=
                  div_le_div_of_nonneg_left hCv.le (rpow_pos_of_pos hlogt_pos A) hlogA10
              _ = Cv * (1 / (Real.log t) ^ A) := by ring
              _ ≤ Cv * ((2 : ℝ) ^ A / (Real.log x) ^ A) :=
                  mul_le_mul_of_nonneg_left hinv_logtA hCv.le
              _ = Cv * (2 : ℝ) ^ A / (Real.log x) ^ A := by ring
          have h2b : (Q : ℝ) / (Real.sqrt t * Real.log t) ≤ 1 / (Real.log x) ^ A := by
            have hden : x ^ (β / 2) ≤ Real.sqrt t * Real.log t :=
              le_trans hsqrtT_le (le_mul_of_one_le_right (Real.sqrt_nonneg t) hlogt1)
            have hexp : θ + η / 2 = β / 2 := by rw [hηdef, hβdef]; ring
            calc (Q : ℝ) / (Real.sqrt t * Real.log t)
                ≤ x ^ θ / x ^ (β / 2) :=
                  div_le_div₀ (rpow_nonneg hx0.le θ) hQ_le_xθ (rpow_pos_of_pos hx0 _) hden
              _ = 1 / x ^ (η / 2) := by
                  rw [← hexp, rpow_add hx0]
                  field_simp [(rpow_pos_of_pos hx0 θ).ne', (rpow_pos_of_pos hx0 (η / 2)).ne']
              _ ≤ 1 / (Real.log x) ^ A :=
                  div_le_div_of_nonneg_left zero_le_one hlogA_pos hlogA_le_xη2
          have htot_t : ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ ≤ 24 * Real.log t := by
            linarith [htot, hlogt_ge]
          have h2c : (Stage11BombieriVinogradov.psiAPMaxError 1 t / (t * (Real.log t) ^ 2)) *
                (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) ≤
              24 * Cv * (2 : ℝ) ^ A / (Real.log x) ^ A := by
            have hbv1 := hBV1_on t htT
            have hlogA9 : (Real.log t) ^ A ≤ (Real.log t) ^ (A + 8) * Real.log t := by
              calc (Real.log t) ^ A ≤ (Real.log t) ^ (A + 8) :=
                    rpow_le_rpow_of_exponent_le hlogt1 (by linarith)
                _ ≤ (Real.log t) ^ (A + 8) * Real.log t :=
                    le_mul_of_one_le_right (rpow_nonneg hlogt_pos.le _) hlogt1
            have hfac_nn : (0 : ℝ) ≤ Stage11BombieriVinogradov.psiAPMaxError 1 t /
                (t * (Real.log t) ^ 2) :=
              div_nonneg (Stage11BombieriVinogradov.psiAPMaxError_nonneg 1 t) (by positivity)
            calc (Stage11BombieriVinogradov.psiAPMaxError 1 t / (t * (Real.log t) ^ 2)) *
                  (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹)
                ≤ (Stage11BombieriVinogradov.psiAPMaxError 1 t / (t * (Real.log t) ^ 2)) *
                    (24 * Real.log t) := mul_le_mul_of_nonneg_left htot_t hfac_nn
              _ ≤ ((Cv * t / (Real.log t) ^ (A + 8)) / (t * (Real.log t) ^ 2)) *
                    (24 * Real.log t) :=
                  mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hbv1 (by positivity))
                    (by positivity)
              _ = 24 * Cv / ((Real.log t) ^ (A + 8) * Real.log t) := by
                  field_simp [ht0.ne', (rpow_pos_of_pos hlogt_pos (A + 8)).ne', hlogt_pos.ne']
              _ ≤ 24 * Cv / (Real.log t) ^ A :=
                  div_le_div_of_nonneg_left (by positivity) (rpow_pos_of_pos hlogt_pos A) hlogA9
              _ = 24 * Cv * (1 / (Real.log t) ^ A) := by ring
              _ ≤ 24 * Cv * ((2 : ℝ) ^ A / (Real.log x) ^ A) :=
                  mul_le_mul_of_nonneg_left hinv_logtA (by positivity)
              _ = 24 * Cv * (2 : ℝ) ^ A / (Real.log x) ^ A := by ring
          have h2d : (1 / (Real.sqrt t * Real.log t)) *
                (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) ≤ 24 / (Real.log x) ^ A := by
            have hη_le_β : η / 2 ≤ β / 2 := by rw [hηdef, hβdef]; linarith
            have hxη_le_sq : x ^ (η / 2) ≤ Real.sqrt t :=
              le_trans (rpow_le_rpow_of_exponent_le hx1 hη_le_β) hsqrtT_le
            calc (1 / (Real.sqrt t * Real.log t)) *
                  (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹)
                ≤ (1 / (Real.sqrt t * Real.log t)) * (24 * Real.log t) :=
                  mul_le_mul_of_nonneg_left htot_t (by positivity)
              _ = 24 / Real.sqrt t := by
                  field_simp [(Real.sqrt_pos.mpr ht0).ne', hlogt_pos.ne']
              _ ≤ 24 / x ^ (η / 2) :=
                  div_le_div_of_nonneg_left (by norm_num) (rpow_pos_of_pos hx0 _) hxη_le_sq
              _ ≤ 24 / (Real.log x) ^ A :=
                  div_le_div_of_nonneg_left (by norm_num) hlogA_pos hlogA_le_xη2
          calc (∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t) /
                (t * (Real.log t) ^ 2) +
                (Q : ℝ) / (Real.sqrt t * Real.log t) +
                (Stage11BombieriVinogradov.psiAPMaxError 1 t / (t * (Real.log t) ^ 2)) *
                  (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) +
                (1 / (Real.sqrt t * Real.log t)) *
                  (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹)
              ≤ Cv * (2 : ℝ) ^ A / (Real.log x) ^ A + 1 / (Real.log x) ^ A +
                24 * Cv * (2 : ℝ) ^ A / (Real.log x) ^ A + 24 / (Real.log x) ^ A :=
                add_le_add (add_le_add (add_le_add h2a h2b) h2c) h2d
            _ = M := by rw [hMdef]; ring
        have hconst : ∫ _t in T..x, M = (x - T) * M := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
        have hMnn : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
        calc ∫ t in T..x, ∑ q ∈ Finset.Icc 1 Q, F q t
            ≤ (x - T) * M := by rw [← hconst]; exact hmono
          _ ≤ x * M := mul_le_mul_of_nonneg_right (by linarith [hT2]) hMnn
          _ = (25 * Cv * (2 : ℝ) ^ A + 25) * x / (Real.log x) ^ A := by rw [hMdef]; ring
      -- Step 4: Lower integral `∫_2^T ∑_{q=1}^Q F q t dt`
      have hPiece3 : ∫ t in (2 : ℝ)..T, ∑ q ∈ Finset.Icc 1 Q, F q t ≤
          178 * x / (Real.log x) ^ A := by
        let G : ℝ → ℝ := fun t =>
          172 * Real.log x + (2 * (Q : ℝ)) * (1 / t) + (2 * (Q : ℝ)) * (1 / Real.sqrt t)
        have hintInv : IntervalIntegrable (fun t : ℝ => 1 / t) volume (2 : ℝ) T := by
          refine ContinuousOn.intervalIntegrable ?_
          rw [Set.uIcc_of_le hT2]
          exact continuousOn_const.div continuousOn_id fun t ht => by linarith [ht.1]
        have hintSqrt : IntervalIntegrable (fun t : ℝ => 1 / Real.sqrt t) volume (2 : ℝ) T := by
          refine ContinuousOn.intervalIntegrable ?_
          rw [Set.uIcc_of_le hT2]
          exact continuousOn_const.div Real.continuous_sqrt.continuousOn fun t ht =>
            (Real.sqrt_pos.mpr (by linarith [ht.1])).ne'
        have hintG : IntervalIntegrable G volume (2 : ℝ) T :=
          (intervalIntegrable_const.add (hintInv.const_mul _)).add (hintSqrt.const_mul _)
        have hmono : ∫ t in (2 : ℝ)..T, ∑ q ∈ Finset.Icc 1 Q, F q t ≤ ∫ t in (2 : ℝ)..T, G t := by
          refine intervalIntegral.integral_mono_on hT2 (hintSum le_rfl hT2) hintG fun t ht => ?_
          have ht2 : (2 : ℝ) ≤ t := ht.1
          have ht0 : (0 : ℝ) < t := by linarith
          have hlogt_ge : (1 : ℝ) / 2 ≤ Real.log t :=
            le_trans half_le_log_two (Real.log_le_log (by norm_num) ht2)
          have hlogt_pos : (0 : ℝ) < Real.log t := by linarith
          have hsq_pos : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
          have hsq_mul : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
          have hsq_le_t : Real.sqrt t ≤ t := by
            refine Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
          have hsum_psi : ∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t ≤
              t * Real.log t * (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ))⁻¹) + (Q : ℝ) * Real.log t +
              t * (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) := by
            have hcard : ((Finset.Icc 1 Q).card : ℝ) = (Q : ℝ) := by
              have h := Nat.card_Icc 1 Q; exact_mod_cast (by omega : (Finset.Icc 1 Q).card = Q)
            calc ∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t
                ≤ ∑ q ∈ Finset.Icc 1 Q, ((t / (q : ℝ) + 1) * Real.log t +
                    t / ((q.totient : ℕ) : ℝ)) :=
                  Finset.sum_le_sum fun q hq => psiAPMaxError_le_class (Finset.mem_Icc.mp hq).1 ht2
              _ = ∑ q ∈ Finset.Icc 1 Q,
                    ((t * Real.log t) * ((q : ℝ))⁻¹ + Real.log t + t * ((q.totient : ℕ) : ℝ)⁻¹) :=
                  Finset.sum_congr rfl fun q _ => by ring
              _ = t * Real.log t * (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ))⁻¹) + (Q : ℝ) * Real.log t +
                    t * (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) := by
                  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
                    hcard]
          have hpsi1_t : Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t ≤
              5 * t * Real.log t := by
            have h1 : Stage11BombieriVinogradov.psiAPMaxError 1 t ≤ (t + 1) * Real.log t + t := by
              simpa using psiAPMaxError_le_class one_pos ht2
            have h2 : t ≤ 2 * t * Real.log t := by nlinarith [hlogt_ge, ht0]
            have h3 : Real.sqrt t * Real.log t ≤ t * Real.log t :=
              mul_le_mul_of_nonneg_right hsq_le_t hlogt_pos.le
            nlinarith [h1, h2, h3, hlogt_pos, ht2]
          have hrew : ∑ q ∈ Finset.Icc 1 Q, F q t =
              (∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t) /
                (t * (Real.log t) ^ 2) +
              (Q : ℝ) / (Real.sqrt t * Real.log t) +
              ((Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) /
                (t * (Real.log t) ^ 2)) * (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) := by
            have hcard : ((Finset.Icc 1 Q).card : ℝ) = (Q : ℝ) := by
              have h := Nat.card_Icc 1 Q; exact_mod_cast (by omega : (Finset.Icc 1 Q).card = Q)
            have hsq_div : Real.sqrt t * Real.log t / (t * (Real.log t) ^ 2) =
                1 / (Real.sqrt t * Real.log t) := by
              rw [div_eq_div_iff (by positivity) (by positivity)]
              calc Real.sqrt t * Real.log t * (Real.sqrt t * Real.log t)
                  = (Real.sqrt t * Real.sqrt t) * (Real.log t) ^ 2 := by ring
                _ = 1 * (t * (Real.log t) ^ 2) := by rw [hsq_mul]; ring
            dsimp only [F]
            simp_rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
              hcard, div_eq_mul_inv, ← Finset.mul_sum]
            rw [show ((∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t) +
                  (Q : ℝ) * (Real.sqrt t * Real.log t) +
                  (Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) *
                    ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) * (t * (Real.log t) ^ 2)⁻¹ =
                (∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t) *
                  (t * (Real.log t) ^ 2)⁻¹ +
                (Q : ℝ) * (Real.sqrt t * Real.log t / (t * (Real.log t) ^ 2)) +
                ((Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) *
                  (t * (Real.log t) ^ 2)⁻¹) *
                  (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) by ring,
              hsq_div]
            ring
          rw [hrew]
          have h3a : (∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t) /
                (t * (Real.log t) ^ 2) ≤ 52 * Real.log x + (2 * (Q : ℝ)) * (1 / t) := by
            have hstep : (∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t) /
                  (t * (Real.log t) ^ 2) ≤
                (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ))⁻¹) / Real.log t +
                (Q : ℝ) / (t * Real.log t) +
                (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) / (Real.log t) ^ 2 := by
              calc (∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t) /
                    (t * (Real.log t) ^ 2)
                  ≤ (t * Real.log t * (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ))⁻¹) + (Q : ℝ) * Real.log t +
                      t * (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹)) /
                    (t * (Real.log t) ^ 2) :=
                    div_le_div_of_nonneg_right hsum_psi (by positivity)
                _ = (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ))⁻¹) / Real.log t +
                    (Q : ℝ) / (t * Real.log t) +
                    (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) / (Real.log t) ^ 2 := by
                    field_simp [ht0.ne', hlogt_pos.ne']
            have hA1 : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ))⁻¹) / Real.log t ≤ 4 * Real.log x := by
              rw [div_le_iff₀ hlogt_pos]; nlinarith [hharm, hlogt_ge, hlogx_pos]
            have hA2 : (Q : ℝ) / (t * Real.log t) ≤ (2 * (Q : ℝ)) * (1 / t) := by
              rw [div_le_iff₀ (mul_pos ht0 hlogt_pos)]
              have heq : (2 * (Q : ℝ)) * (1 / t) * (t * Real.log t) =
                  (Q : ℝ) * (2 * Real.log t) := by field_simp [ht0.ne']
              rw [heq]
              nlinarith [hlogt_ge, (Nat.cast_nonneg (α := ℝ) Q)]
            have hA3 : (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) / (Real.log t) ^ 2 ≤
                48 * Real.log x := by
              rw [div_le_iff₀ (sq_pos_of_pos hlogt_pos)]
              have hsqlog : (1 : ℝ) / 4 ≤ (Real.log t) ^ 2 := by nlinarith [hlogt_ge]
              nlinarith [htot, hsqlog, hlogx_pos]
            linarith
          have h3b : (Q : ℝ) / (Real.sqrt t * Real.log t) ≤ (2 * (Q : ℝ)) * (1 / Real.sqrt t) := by
            rw [div_le_iff₀ (mul_pos hsq_pos hlogt_pos)]
            have heq : (2 * (Q : ℝ)) * (1 / Real.sqrt t) * (Real.sqrt t * Real.log t) =
                (Q : ℝ) * (2 * Real.log t) := by field_simp [hsq_pos.ne']
            rw [heq]
            nlinarith [hlogt_ge, (Nat.cast_nonneg (α := ℝ) Q)]
          have h3c : ((Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) /
                (t * (Real.log t) ^ 2)) * (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) ≤
              120 * Real.log x := by
            have hfrac : (Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) /
                (t * (Real.log t) ^ 2) ≤ 10 := by
              calc (Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) /
                    (t * (Real.log t) ^ 2)
                  ≤ (5 * t * Real.log t) / (t * (Real.log t) ^ 2) :=
                    div_le_div_of_nonneg_right hpsi1_t (by positivity)
                _ = 5 / Real.log t := by field_simp [ht0.ne', hlogt_pos.ne']
                _ ≤ 10 := by rw [div_le_iff₀ hlogt_pos]; linarith [hlogt_ge]
            have htot_nn : (0 : ℝ) ≤ ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ :=
              Finset.sum_nonneg fun q _ => by positivity
            calc ((Stage11BombieriVinogradov.psiAPMaxError 1 t + Real.sqrt t * Real.log t) /
                  (t * (Real.log t) ^ 2)) * (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹)
                ≤ 10 * (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) :=
                  mul_le_mul_of_nonneg_right hfrac htot_nn
              _ ≤ 10 * (12 * Real.log x) := mul_le_mul_of_nonneg_left htot (by norm_num)
              _ = 120 * Real.log x := by ring
          dsimp only [G]
          linarith
        have hGint : ∫ t in (2 : ℝ)..T, G t =
            (T - 2) * (172 * Real.log x) +
            (2 * (Q : ℝ)) * (∫ t in (2 : ℝ)..T, (1 / t)) +
            (2 * (Q : ℝ)) * (∫ t in (2 : ℝ)..T, (1 / Real.sqrt t)) := by
          dsimp only [G]
          rw [intervalIntegral.integral_add
                (intervalIntegrable_const.add (hintInv.const_mul _)) (hintSqrt.const_mul _),
            intervalIntegral.integral_add intervalIntegrable_const (hintInv.const_mul _),
            intervalIntegral.integral_const, smul_eq_mul,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        have h3_1 : (T - 2) * (172 * Real.log x) ≤ 172 * x / (Real.log x) ^ A := by
          calc (T - 2) * (172 * Real.log x)
              ≤ T * (172 * Real.log x) := by nlinarith [hlogx_pos]
            _ = 172 * (x ^ (1 - η) * Real.log x) := by rw [hT_eq]; ring
            _ ≤ 172 * (x / (Real.log x) ^ A) := mul_le_mul_of_nonneg_left hx1η_log_le (by norm_num)
            _ = 172 * x / (Real.log x) ^ A := by ring
        have h3_2 : (2 * (Q : ℝ)) * (∫ t in (2 : ℝ)..T, (1 / t)) ≤ 2 * x / (Real.log x) ^ A := by
          have hlogT : Real.log T ≤ Real.log x := Real.log_le_log (by linarith) hTx
          have hxθ_le : x ^ θ ≤ x ^ (1 - η) :=
            rpow_le_rpow_of_exponent_le hx1 (by rw [hηdef]; linarith)
          calc (2 * (Q : ℝ)) * (∫ t in (2 : ℝ)..T, (1 / t))
              ≤ (2 * (Q : ℝ)) * Real.log T :=
                mul_le_mul_of_nonneg_left (integral_one_div_le hT2) (by positivity)
            _ ≤ (2 * x ^ (1 - η)) * Real.log x :=
                mul_le_mul (by linarith [hQ_le_xθ, hxθ_le]) hlogT
                  (Real.log_nonneg (by linarith)) (by positivity)
            _ = 2 * (x ^ (1 - η) * Real.log x) := by ring
            _ ≤ 2 * (x / (Real.log x) ^ A) := mul_le_mul_of_nonneg_left hx1η_log_le (by norm_num)
            _ = 2 * x / (Real.log x) ^ A := by ring
        have h3_3 : (2 * (Q : ℝ)) * (∫ t in (2 : ℝ)..T, (1 / Real.sqrt t)) ≤
            4 * x / (Real.log x) ^ A := by
          have hsqrtT : Real.sqrt T = x ^ (β / 2) := by
            rw [Real.sqrt_eq_rpow, hTdef, ← rpow_mul hx0.le]; congr 1; ring
          have hexp : θ + β / 2 ≤ 1 - η := by rw [hβdef, hηdef]; linarith
          calc (2 * (Q : ℝ)) * (∫ t in (2 : ℝ)..T, (1 / Real.sqrt t))
              ≤ (2 * (Q : ℝ)) * (2 * Real.sqrt T) :=
                mul_le_mul_of_nonneg_left (integral_one_div_sqrt_le hT2) (by positivity)
            _ = 4 * ((Q : ℝ) * x ^ (β / 2)) := by rw [hsqrtT]; ring
            _ ≤ 4 * (x ^ θ * x ^ (β / 2)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hQ_le_xθ (rpow_nonneg hx0.le _)) (by norm_num)
            _ = 4 * x ^ (θ + β / 2) := by rw [← rpow_add hx0]
            _ ≤ 4 * x ^ (1 - η) :=
                mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le hx1 hexp) (by norm_num)
            _ ≤ 4 * (x / (Real.log x) ^ A) := mul_le_mul_of_nonneg_left hx1η_le (by norm_num)
            _ = 4 * x / (Real.log x) ^ A := by ring
        calc ∫ t in (2 : ℝ)..T, ∑ q ∈ Finset.Icc 1 Q, F q t
            ≤ ∫ t in (2 : ℝ)..T, G t := hmono
          _ = (T - 2) * (172 * Real.log x) +
              (2 * (Q : ℝ)) * (∫ t in (2 : ℝ)..T, (1 / t)) +
              (2 * (Q : ℝ)) * (∫ t in (2 : ℝ)..T, (1 / Real.sqrt t)) := hGint
          _ ≤ 172 * x / (Real.log x) ^ A + 2 * x / (Real.log x) ^ A +
              4 * x / (Real.log x) ^ A := add_le_add (add_le_add h3_1 h3_2) h3_3
          _ = 178 * x / (Real.log x) ^ A := by ring
      -- Combine Pieces 1, 2, 3
      calc ∑ q ∈ Finset.Icc 1 Q,
              ⨆ a : (ZMod q)ˣ, |((Real.primeCountingZMod x q (a : ZMod q) : ℕ) : ℝ) -
                _root_.pi x / ((q.totient : ℕ) : ℝ)|
          ≤ (∑ q ∈ Finset.Icc 1 Q,
              (Stage11BombieriVinogradov.psiAPMaxError q x + Real.sqrt x * Real.log x +
                (Stage11BombieriVinogradov.psiAPMaxError 1 x + Real.sqrt x * Real.log x) /
                  ((q.totient : ℕ) : ℝ)) / Real.log x) +
            (∫ t in (2 : ℝ)..T, ∑ q ∈ Finset.Icc 1 Q, F q t) +
            (∫ t in T..x, ∑ q ∈ Finset.Icc 1 Q, F q t) := hsum_ub
        _ ≤ (13 * Cv + 13) * x / (Real.log x) ^ A +
            178 * x / (Real.log x) ^ A +
            (25 * Cv * (2 : ℝ) ^ A + 25) * x / (Real.log x) ^ A :=
            add_le_add (add_le_add hPiece1 hPiece3) hPiece2
        _ = K * x / (Real.log x) ^ A := by rw [hKdef]; ring
    obtain ⟨K, hK1, hK⟩ := hasym
    -- the small-`x` guard
    set c_small : ℝ := (X₀ ^ θ + 1) * (2 * (X₀ + 2)) * ((Real.log X₀) ^ A / 3)
      with hcsmalldef
    have hcsmallpos : (0 : ℝ) < c_small := by
      dsimp only [c_small]
      have h1 : (0 : ℝ) < X₀ ^ θ := rpow_pos_of_pos hX₀pos θ
      have h2 : (1 : ℝ) ≤ Real.log X₀ := by
        have h5 : Real.log (Real.exp 1) ≤ Real.log X₀ :=
          Real.log_le_log (Real.exp_pos 1) hX₀e
        rwa [Real.log_exp (1 : ℝ)] at h5
      have h3 : (0 : ℝ) < Real.log X₀ ^ A := by
        refine rpow_pos_of_pos (by linarith : (0 : ℝ) < Real.log X₀) A
      positivity
    set c : ℝ := max K c_small with hcdef
    have hcpos : (0 : ℝ) < c := lt_of_lt_of_le hcsmallpos (le_max_right _ _)
    refine ⟨c, hcpos, fun x hx3 => ?_⟩
    by_cases hxX : X₀ ≤ x
    · -- the asymptotic branch
      refine le_trans (hK x hxX) ?_
      have hxpos : (0 : ℝ) < x ^ A := rpow_pos_of_pos (by linarith : (0 : ℝ) < x) A
      have hKle : K ≤ c := le_max_left _ _
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKle (by linarith : (0 : ℝ) ≤ x))
        (rpow_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ x)) A)
    · -- the small-`x` branch: `x < X₀`, crude constant bound
      have hxX₀ : x < X₀ := not_le.mp hxX
      have hx1 : (1 : ℝ) ≤ x := by linarith
      have hM : ∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊,
          ⨆ a : (ZMod q)ˣ, |((Real.primeCountingZMod x q (a : ZMod q) : ℕ) : ℝ) -
            _root_.pi x / ((q.totient : ℕ) : ℝ)| ≤
          (X₀ ^ θ + 1) * (2 * (X₀ + 2)) := by
        have hQx1 : 1 ≤ ⌊x ^ θ⌋₊ := by
          have h1 : (1 : ℝ) ^ θ ≤ x ^ θ :=
            Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hx1 hθpos.le
          rw [one_rpow] at h1
          exact (Nat.one_le_floor_iff (x := x ^ θ)).mpr h1
        have hcard : (Finset.Icc 1 ⌊x ^ θ⌋₊).card = ⌊x ^ θ⌋₊ := by
          have h5 : (Finset.Icc 1 ⌊x ^ θ⌋₊).card = ⌊x ^ θ⌋₊ + 1 - 1 := Nat.card_Icc 1 ⌊x ^ θ⌋₊
          omega
        have hpcBound : ∀ n : ℕ, ((Nat.primeCounting n : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) + 1 := by
          intro n
          have h2 : Nat.primeCounting n ≤ n + 1 := by
            rw [show Nat.primeCounting n = Nat.count Nat.Prime (n + 1) from rfl]
            exact Nat.count_le Nat.Prime
          exact_mod_cast h2
        have hunit : ∀ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, ∀ a : (ZMod q)ˣ,
            |((Real.primeCountingZMod x q (a : ZMod q) : ℕ) : ℝ) -
              _root_.pi x / ((q.totient : ℕ) : ℝ)| ≤
            2 * ((⌊x⌋₊ : ℕ) : ℝ) + 2 := by
          intro q hq a
          have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
          have hqpos' : 1 ≤ q := hqpos
          have hne : NeZero q := ⟨by omega⟩
          have hcast : Real.primeCountingZMod x q (a : ZMod q) =
              Stage2DirichletAP.primeCountAP q (ZMod.val (a : ZMod q)) x := by
            have h := primeCountingZMod_eq_primeCountAP (q := q) x (ZMod.val (a : ZMod q))
            rwa [← zmod_eq_val_cast (a : ZMod q)] at h
          have hφpos : (0 : ℝ) < ((q.totient : ℕ) : ℝ) := by
            exact_mod_cast Nat.totient_pos.mpr hqpos
          have hφ1 : (1 : ℝ) ≤ ((q.totient : ℕ) : ℝ) := by
            exact_mod_cast Nat.totient_pos.mpr hqpos
          have hpc := primeCountAP_le_global q (ZMod.val (a : ZMod q)) x
          have hpi : _root_.pi x = ((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) := rfl
          rw [hcast, hpi]
          have hunn : (0 : ℝ) ≤ ((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) := by positivity
          have hvnn : (0 : ℝ) ≤ ((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) /
              ((q.totient : ℕ) : ℝ) :=
            div_nonneg hunn hφpos.le
          have hve : ((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) /
              ((q.totient : ℕ) : ℝ) ≤ ((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) :=
            div_le_self hunn hφ1
          calc |((Stage2DirichletAP.primeCountAP q (ZMod.val (a : ZMod q)) x : ℕ) : ℝ) -
                ((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) / ((q.totient : ℕ) : ℝ)|
              ≤ ((Stage2DirichletAP.primeCountAP q (ZMod.val (a : ZMod q)) x : ℕ) : ℝ) +
                  (((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) / ((q.totient : ℕ) : ℝ)) := by
                rw [abs_le]
                constructor <;> nlinarith [hunn, hvnn]
            _ ≤ (((⌊x⌋₊ : ℕ) : ℝ) + 1) + (((⌊x⌋₊ : ℕ) : ℝ) + 1) := by
                refine add_le_add ?_ ?_
                · exact_mod_cast le_trans hpc (Nat.count_le Nat.Prime)
                · exact le_trans hve (hpcBound ⌊x⌋₊)
            _ = 2 * ((⌊x⌋₊ : ℕ) : ℝ) + 2 := by ring
        -- sum over `q` and the crude monotone pieces
        calc ∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊,
                ⨆ a : (ZMod q)ˣ, |((Real.primeCountingZMod x q (a : ZMod q) : ℕ) : ℝ) -
                  _root_.pi x / ((q.totient : ℕ) : ℝ)|
            ≤ ∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, (2 * ((⌊x⌋₊ : ℕ) : ℝ) + 2) :=
                Finset.sum_le_sum fun q hq => ciSup_le (hunit q hq)
          _ = ((Finset.Icc 1 ⌊x ^ θ⌋₊).card : ℝ) * (2 * ((⌊x⌋₊ : ℕ) : ℝ) + 2) := by
                rw [Finset.sum_const, nsmul_eq_mul]
          _ = ((⌊x ^ θ⌋₊ : ℕ) : ℝ) * (2 * ((⌊x⌋₊ : ℕ) : ℝ) + 2) := by
                rw [show ((Finset.Icc 1 ⌊x ^ θ⌋₊).card : ℝ) = ((⌊x ^ θ⌋₊ : ℕ) : ℝ) by
                  rw [hcard]]
          _ ≤ (x ^ θ + 1) * (2 * (x + 2)) := by
                have hQxθ : ((⌊x ^ θ⌋₊ : ℕ) : ℝ) ≤ x ^ θ :=
                  Nat.floor_le (rpow_nonneg (by linarith : (0 : ℝ) ≤ x) θ)
                have hfx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith : (0 : ℝ) ≤ x)
                have hQxnn : (0 : ℝ) ≤ ((⌊x ^ θ⌋₊ : ℕ) : ℝ) := by positivity
                have hfxnn : (0 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by positivity
                have hxθnn : (0 : ℝ) ≤ x ^ θ := rpow_nonneg (by linarith : (0 : ℝ) ≤ x) θ
                have hprod : ((⌊x ^ θ⌋₊ : ℕ) : ℝ) * ((⌊x⌋₊ : ℕ) : ℝ) ≤ x ^ θ * x :=
                  mul_le_mul hQxθ hfx hfxnn hxθnn
                nlinarith [hprod, hQxθ, hfx, hxθnn]
          _ ≤ (X₀ ^ θ + 1) * (2 * (X₀ + 2)) := by
                have hxθX : x ^ θ ≤ X₀ ^ θ :=
                  Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ x) hxX₀.le hθpos.le
                have hxX2 : x + 2 ≤ X₀ + 2 := by linarith
                exact mul_le_mul (add_le_add_left hxθX 1)
                  (mul_le_mul_of_nonneg_left hxX2 (by norm_num : (0 : ℝ) ≤ 2))
                  (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
                    (by linarith : (0 : ℝ) ≤ x + 2))
                  (add_nonneg (rpow_nonneg (by linarith : (0 : ℝ) ≤ X₀) θ) zero_le_one)
      refine le_trans hM ?_
      have hlxX₀ : Real.log x ≤ Real.log X₀ := Real.log_le_log (by linarith) hxX₀.le
      have hMpos : (0 : ℝ) ≤ (X₀ ^ θ + 1) * (2 * (X₀ + 2)) := by
        have : (0 : ℝ) < X₀ ^ θ := rpow_pos_of_pos hX₀pos θ
        positivity
      have hlogpos : (0 : ℝ) < (Real.log x) ^ A :=
        rpow_pos_of_pos (by
          have hthis : Real.log (Real.exp 1) ≤ Real.log x :=
            Real.log_le_log (Real.exp_pos 1) (by
              have hexp : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
              linarith)
          rw [Real.log_exp (1 : ℝ)] at hthis
          linarith) A
      have hkey : (X₀ ^ θ + 1) * (2 * (X₀ + 2)) * (Real.log x) ^ A ≤
          c_small * x := by
        have hlogX : (Real.log x) ^ A ≤ (Real.log X₀) ^ A :=
          rpow_le_rpow (Real.log_nonneg hx1) hlxX₀ (by linarith : (0 : ℝ) ≤ A)
        have hlogXnn : (0 : ℝ) ≤ (Real.log X₀) ^ A :=
          rpow_nonneg (Real.log_nonneg (by
            have h4 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
            have h5 : Real.log (Real.exp 1) ≤ Real.log X₀ :=
              Real.log_le_log (Real.exp_pos 1) hX₀e
            rw [Real.log_exp (1 : ℝ)] at h5
            linarith)) A
        have hL : (0 : ℝ) ≤ (X₀ ^ θ + 1) * (2 * (X₀ + 2)) * (Real.log X₀) ^ A :=
          mul_nonneg hMpos hlogXnn
        have h4 : (X₀ ^ θ + 1) * (2 * (X₀ + 2)) * (Real.log X₀) ^ A * 3 ≤
            (X₀ ^ θ + 1) * (2 * (X₀ + 2)) * (Real.log X₀) ^ A * x := by
          nlinarith [hL, hx3]
        have hfinal : (X₀ ^ θ + 1) * (2 * (X₀ + 2)) * (Real.log x) ^ A * 3 ≤
            ((X₀ ^ θ + 1) * (2 * (X₀ + 2)) * (Real.log X₀ ^ A / 3) * x) * 3 := by
          have hring : ((X₀ ^ θ + 1) * (2 * (X₀ + 2)) * (Real.log X₀ ^ A / 3) * x) * 3 =
              (X₀ ^ θ + 1) * (2 * (X₀ + 2)) * (Real.log X₀) ^ A * x := by ring
          rw [hring]
          have hpre : (X₀ ^ θ + 1) * (2 * (X₀ + 2)) * (Real.log x) ^ A ≤
              (X₀ ^ θ + 1) * (2 * (X₀ + 2)) * (Real.log X₀) ^ A :=
            mul_le_mul_of_nonneg_left hlogX hMpos
          calc (X₀ ^ θ + 1) * (2 * (X₀ + 2)) * (Real.log x) ^ A * 3 ≤
                (X₀ ^ θ + 1) * (2 * (X₀ + 2)) * (Real.log X₀) ^ A * 3 :=
                  mul_le_mul_of_nonneg_right hpre (by norm_num : (0 : ℝ) ≤ 3)
            _ ≤ (X₀ ^ θ + 1) * (2 * (X₀ + 2)) * (Real.log X₀) ^ A * x := h4
        exact le_of_mul_le_mul_right hfinal (by norm_num : (0 : ℝ) < 3)
      calc (X₀ ^ θ + 1) * (2 * (X₀ + 2))
          = (X₀ ^ θ + 1) * (2 * (X₀ + 2)) * (Real.log x) ^ A / (Real.log x) ^ A :=
            (mul_div_cancel_right₀ _ hlogpos.ne').symm
        _ ≤ c_small * x / (Real.log x) ^ A := by
            exact div_le_div_of_nonneg_right hkey hlogpos.le
        _ ≤ c * x / (Real.log x) ^ A := by
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
              (le_max_right _ _) (by linarith : (0 : ℝ) ≤ x)) hlogpos.le

end MaynardDock
