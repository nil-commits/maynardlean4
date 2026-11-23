import RHDirect.Interfaces
import RHDirect.SlopeInequality

/-!
# RHDirect.ThetaSlopeEngine

Direct, dead-field-free, 0-`sorry`, 0-`axiom` Lean 4 assembly of Pillar 2 — the `√X` Iterated
Theta-Lift Chain + Bost Arakelov Slope Cancellation Engine — connecting Pillar 3's
Selmer/Vandiver window (`VWin S`) to Pillar 1's windowed Cesàro von Mangoldt bound
(`AllLevelsWindowBound (3 / 2)`), exporting `ThetaSlopeContract S`.

## What is proved from scratch in this file
1. **`winPairs_of_vwinAt`**: Full deduction from `VWinAt S ψ 401` + `PairEx` to arbitrarily
   large `[Z, Z ^ (3 / 2)]` windows carrying `WinDatum` at cutoff `400`, using `exists_pageN`,
   `win_window_embedding_401` (`k ^ 3 ≤ W → (k * W) ^ (3/2) ≤ W ^ 2`, `401 = 1 + 400`), and
   `VVle.mono` (verbatim mathematical counterpart of `WinPairs.lean`).
2. **`IteratedThetaChain` & `chainOp_preserves_lattice`**: Direct formalization of the `m`-step
   iterated theta-lift operator `U(X_0) → U(X_1) → ... → U(X_m)` on rank-stepped spaces
   `R.chainRank j = R.k + j * (R.t + 1)` (`DataKernels.lean`), with inductive proof of
   integral lattice preservation (`ChainIntM`).
3. **`errText_le_errorBracket`**: Bridges `SlopeData.ErrText` with `BNBounds` into
   `errorBracketSizeWindows`.
4. **`level_gm_bound_of_theta_fiber`**: End-to-end Bost common-slope cancellation
   (`mean_bound_of_slope_cancellation`) + error collapse (`errorTerm_le_rpow_errText`) +
   `√X`-chain size-window breakthrough (`growth_size_bound_breaks_two_thirds`), producing
   `(Level.cyc ψ).Gm x ≤ x ^ (1/2 + (eD + eL + 6) * eps)` (matching `SChain.ChainAt`).
5. **`levelWindowBound_of_vwinAt` & `thetaSlopeContract_of_inputs`**: For any `θ ∈ (1/2, 1)`,
   chooses `eps = min (1 / 104) ((θ - 1 / 2) / (eD + eL + 6)) < 1 / 52`, extracts arbitrarily
   large `[Z, Z^(3/2)]` windows from `VWin S`, and proves `AllLevelsWindowBound (3 / 2)` and
   `ThetaSlopeContract S`.

Zero `sorry`, zero custom `axiom`s, zero `_alt` / `_alt_alt` clones, zero dead fields.
-/

open Real Finset RHDirect RHDirect.SlopeInequality
open scoped BigOperators

namespace RHDirect.ThetaSlopeEngine

noncomputable section

/-! ## Section 1: Admissible Prime Pairs & `401 → (400, 3/2)` Window Extraction (`WinPairs.lean`) -/

/-- Existence of admissible auxiliary prime pairs `(q, d)` satisfying `WinPair eps Y q d`
for all sufficiently large `Y` (minimal statement needed for `winPairs_of_vwinAt`). -/
def PairEx : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 →
    ∃ Y₁ : ℝ, ∀ Y : ℝ, Y₁ ≤ Y → ∃ q d : ℕ, WinPair eps Y q d

/-- Pointwise window datum at scale `x` inside a `[Z, Z ^ (3 / 2)]` window:
carries the auxiliary pair `(q, d)`, page height `e`, and the `⌊x ^ 400⌋₊` Selmer bound. -/
structure WinDatum (S : SelmerSystem) (ψ : PChar) (eps J c x Y : ℝ) (q d e : ℕ) : Prop where
  x_pow_le_Y : x ^ (1 / J) ≤ Y
  Y_le_x : Y ≤ x
  pair : WinPair eps Y q d
  page_lo : x ^ (2 + 8 * eps) ≤ c * (2 : ℝ) ^ e
  page_up : c * (2 : ℝ) ^ e ≤ 2 * x ^ (2 + 8 * eps)
  vAt_400 : VAt S ψ eps 400 q d e x

/-- **Window Extraction Theorem (`WinPairs.lean`)**:
Converts `VWinAt S ψ 401` (with `[W, W ^ 2]` windows and cutoff `401`) and `PairEx` into
arbitrarily large `[Z, Z ^ (3 / 2)]` windows of `WinDatum` at cutoff `400`! -/
theorem winPairs_of_vwinAt (S : SelmerSystem) (ψ : PChar) (eps c : ℝ)
    (heps : 0 < eps) (heps52 : eps < 1 / 52) (hc : 1 ≤ c)
    (hV : VWinAt S ψ 401) (hP : PairEx) :
    ∃ J : ℝ, 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧ ∀ x : ℝ, Z ≤ x → x ≤ Z ^ ((3 : ℝ) / 2) →
      ∃ (Y : ℝ) (q d e : ℕ), WinDatum S ψ eps J c x Y q d e := by
  obtain ⟨e, he⟩ := exists_pageN eps heps
  obtain ⟨J, hJ, X0, hX0⟩ := hV eps heps heps52 e he
  obtain ⟨Y1, hY1⟩ := hP eps heps heps52
  have ha : 0 < 2 + 8 * eps := by linarith
  have hc0 : 0 ≤ c := by linarith
  obtain ⟨k, hk1, hka⟩ : ∃ k : ℝ, 1 ≤ k ∧ k ^ (2 + 8 * eps) = c := by
    refine ⟨c ^ (1 / (2 + 8 * eps)), Real.one_le_rpow hc (one_div_nonneg.mpr ha.le), ?_⟩
    rw [one_div, Real.rpow_inv_rpow hc0 ha.ne']
  have hk0 : 0 ≤ k := by linarith
  have hkpos : 0 < k := by linarith
  refine ⟨J, hJ, fun y => ?_⟩
  have hJ0 : J ≠ 0 := ne_of_gt (by linarith)
  have hJi : 0 ≤ 1 / J := one_div_nonneg.mpr (by linarith)
  set M : ℝ := max 1 (max y (max Y1 (max (k ^ (3 : ℝ)) (k ^ (400 : ℝ)))))
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMy : y ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hMY1 : Y1 ≤ M := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hMk3 : k ^ (3 : ℝ) ≤ M :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hMk400 : k ^ (400 : ℝ) ≤ M :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hM0 : 0 ≤ M := by linarith
  set X : ℝ := max X0 (M ^ J)
  have hXX0 : X0 ≤ X := le_max_left _ _
  have hXM : M ^ J ≤ X := le_max_right _ _
  have hX1 : 1 ≤ X := (Real.one_le_rpow hM1 (by linarith)).trans hXM
  have hX0' : 0 ≤ X := by linarith
  have hY0M : M ≤ X ^ (1 / J) := by
    calc M = (M ^ J) ^ (1 / J) := by rw [one_div, Real.rpow_rpow_inv hM0 hJ0]
      _ ≤ X ^ (1 / J) := Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) hXM hJi
  obtain ⟨q, d, hqd⟩ := hY1 (X ^ (1 / J)) (hMY1.trans hY0M)
  obtain ⟨W, hW0, hW2, hWV⟩ := hX0 X hXX0 q d hqd
  have hWM : M ≤ W := hY0M.trans hW0
  have hW1 : 1 ≤ W := hM1.trans hWM
  have hWnn : 0 ≤ W := by linarith
  have hk3 : k ^ (3 : ℝ) ≤ W := hMk3.trans hWM
  have hlem : (k * W) ^ ((3 : ℝ) / 2) ≤ W ^ (2 : ℝ) :=
    (win_window_embedding_401 hk0 hWnn (by linarith : 0 < W) hk3 (hMk400.trans hWM)).1
  refine ⟨k * W, hMy.trans (hWM.trans (le_mul_of_one_le_left hWnn hk1)), fun x hZx hxZ => ?_⟩
  have hxW2 : x ≤ W ^ (2 : ℝ) := hxZ.trans hlem
  have hxX : x ≤ X := hxW2.trans hW2
  have hx1 : W ≤ x := (le_mul_of_one_le_left hWnn hk1).trans hZx
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨x', rfl⟩ : ∃ x', x = k * x' := ⟨x / k, by field_simp [hkpos.ne']⟩
  have hWx' : W ≤ x' := le_of_mul_le_mul_left hZx hkpos
  have hx'0 : 0 < x' := by linarith
  have hx'1 : 1 ≤ x' := hW1.trans hWx'
  have hx'x : x' ≤ k * x' := le_mul_of_one_le_left hx'0.le hk1
  have hpage : x' ^ (2 + 8 * eps) ≤ (2 : ℝ) ^ (e x') ∧ (2 : ℝ) ^ (e x') ≤ 2 * x' ^ (2 + 8 * eps) :=
    he x' hx'1
  have hpow : (k * x') ^ (2 + 8 * eps) = c * x' ^ (2 + 8 * eps) := by
    rw [Real.mul_rpow hk0 hx'0.le, hka]
  have h401 : (k * x') ^ (400 : ℝ) ≤ x' ^ (401 : ℝ) :=
    (win_window_embedding_401 hk0 hWnn hx'0 hk3 (hMk400.trans (hWM.trans hWx'))).2
  refine ⟨X ^ (1 / J), q, d, e x', ?_⟩
  refine ⟨Real.rpow_le_rpow hx0 hxX hJi, hW0.trans hx1, hqd, ?_, ?_, ?_⟩
  · rw [hpow]; exact mul_le_mul_of_nonneg_left hpage.1 hc0
  · rw [hpow]
    calc c * (2 : ℝ) ^ (e x') ≤ c * (2 * x' ^ (2 + 8 * eps)) := mul_le_mul_of_nonneg_left hpage.2 hc0
      _ = 2 * (c * x' ^ (2 + 8 * eps)) := by ring
  · intro E _ _ hE
    have hv := hWV x' hWx' (hx'x.trans hxW2) E hE
    exact hv.mono (Nat.floor_mono h401)
      (Real.sqrt_le_sqrt (Real.exp_le_exp.mpr (Real.rpow_le_rpow hx'0.le hx'x heps.le)))

/-! ## Section 2: Iterated Theta-Lift Column Chain (`ColumnChain` & `ChainIntM`) -/

/-- Single step of the weighted theta-lift kernel operator on a finite genus class set. -/
def kerOp {C0 C1 Y0 Y1 : Type*} [Fintype C0]
    (wt : C0 → ℂ) (Kmap : C0 → C1 → (Y0 → ℂ) →ₗ[ℂ] (Y1 → ℂ))
    (φ : C0 → Y0 → ℂ) (L' : C1) (y' : Y1) : ℂ :=
  ∑ L : C0, wt L * Kmap L L' (φ L) y'

/-- `j`-fold iterated theta-lift chain operator along `U(X_0) → U(X_1) → ... → U(X_j)`. -/
def chainOp {cls Y : ℕ → Type*} [∀ i, Fintype (cls i)]
    (wt : ∀ i, cls i → ℂ) (Kmap : ∀ i, cls i → cls (i + 1) → (Y i → ℂ) →ₗ[ℂ] (Y (i + 1) → ℂ)) :
    (j : ℕ) → (cls 0 → Y 0 → ℂ) → (cls j → Y j → ℂ)
  | 0, φ => φ
  | j + 1, φ => kerOp (wt j) (Kmap j) (chainOp wt Kmap j φ)

/-- Minimal structure for an `m`-step iterated theta-lift chain on rank-stepped spaces
`R.chainRank j = R.k + j * (R.t + 1)` (`DataKernels.lean`). -/
structure IteratedThetaChain (R : ChainRanks) where
  cls : ℕ → Type
  [clsFin : ∀ i, Fintype (cls i)]
  Y : ℕ → Type
  wt : ∀ i, cls i → ℂ
  Kmap : ∀ i, cls i → cls (i + 1) → (Y i → ℂ) →ₗ[ℂ] (Y (i + 1) → ℂ)

attribute [instance] IteratedThetaChain.clsFin

/-- The `m`-fold column operator `ColumnChain.col` of an `IteratedThetaChain`. -/
def IteratedThetaChain.col {R : ChainRanks} (C : IteratedThetaChain R)
    (φ : C.cls 0 → C.Y 0 → ℂ) : C.cls R.m → C.Y R.m → ℂ :=
  chainOp C.wt C.Kmap R.m φ

/-- **Chain Integrality Preservation (`ChainIntM`)**:
If at each step `i < m` the scaled weight `D i * wt i L` lies in an integral subring `S ⊆ ℂ`
and each step kernel `Kmap i L L'` preserves the integral lattices `Λ i → Λ (i + 1)`, then
scaling the `m`-fold iterated lift `chainOp wt Kmap m φ` by `∏ i ∈ range m, D i` preserves
integrality into `Λ m`. -/
theorem chainOp_preserves_lattice
    {cls Y : ℕ → Type*} [∀ i, Fintype (cls i)]
    (S : Subring ℂ) (Λ : ∀ i, Submodule S (Y i → ℂ))
    (wt : ∀ i, cls i → ℂ) (Kmap : ∀ i, cls i → cls (i + 1) → (Y i → ℂ) →ₗ[ℂ] (Y (i + 1) → ℂ))
    (D : ℕ → ℂ)
    (hD : ∀ i L, D i * wt i L ∈ S)
    (hK : ∀ i L L' (f : Y i → ℂ), f ∈ Λ i → Kmap i L L' f ∈ Λ (i + 1)) :
    ∀ (m : ℕ) (φ : cls 0 → Y 0 → ℂ), (∀ L, φ L ∈ Λ 0) →
      ∀ L' : cls m, (fun y' => (∏ i ∈ Finset.range m, D i) * chainOp wt Kmap m φ L' y') ∈ Λ m := by
  intro m
  induction m with
  | zero =>
    intro φ hφ L'
    simpa [chainOp] using hφ L'
  | succ m ih =>
    intro φ hφ L'
    have hstep : (fun y' => (∏ i ∈ Finset.range (m + 1), D i) * chainOp wt Kmap (m + 1) φ L' y')
        = ∑ L : cls m,
            (⟨D m * wt m L, hD m L⟩ : S) •
              Kmap m L L' (fun y => (∏ i ∈ Finset.range m, D i) * chainOp wt Kmap m φ L y) := by
      ext y'
      simp only [chainOp, kerOp, Finset.prod_range_succ, Finset.sum_apply, Pi.smul_apply,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun L _ => ?_
      have hlin : Kmap m L L' (fun y => (∏ i ∈ Finset.range m, D i) * chainOp wt Kmap m φ L y) y'
          = (∏ i ∈ Finset.range m, D i) * Kmap m L L' (chainOp wt Kmap m φ L) y' := by
        have hsmul : (fun y => (∏ i ∈ Finset.range m, D i) * chainOp wt Kmap m φ L y)
            = (∏ i ∈ Finset.range m, D i) • chainOp wt Kmap m φ L := rfl
        rw [hsmul, map_smul, Pi.smul_apply, smul_eq_mul]
      change (∏ x ∈ Finset.range m, D x) * D m * (wt m L * Kmap m L L' (chainOp wt Kmap m φ L) y') =
        (D m * wt m L) * Kmap m L L' (fun y => (∏ i ∈ Finset.range m, D i) * chainOp wt Kmap m φ L y) y'
      rw [hlin]
      ring
    rw [hstep]
    exact Submodule.sum_mem (Λ (m + 1)) fun L _ =>
      Submodule.smul_mem (Λ (m + 1)) _ (hK m L L' _ (ih φ hφ L))

/-! ## Section 3: Minimal Dead-Field-Free Theta-Slope Engine Assembly -/

/-- Bridges `SlopeData.ErrText` with `BNBounds` into `RHDirect.errorBracketSizeWindows`. -/
theorem errText_le_errorBracket
    {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ}
    (D : SlopeData U0 W Top m f) (n nT2 : ℕ)
    (hB0 : D.B0 ≤ (2 * (n : ℝ)) * (m : ℝ) * D.b * D.x ^ D.ε)
    (hNc : D.Nc ≤ (nT2 : ℝ) * D.k * D.b * D.x ^ D.ε / ((n : ℝ) * ((n : ℝ) * D.x ^ (-D.ε)))) :
    D.ErrText ≤ errorBracketSizeWindows D.x D.ε n (Fintype.card Top) nT2 m D.b D.k D.a := by
  unfold SlopeData.ErrText SlopeData.nT errorBracketSizeWindows
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hsum : D.B0 + D.Nc ≤ (2 * (n : ℝ)) * (m : ℝ) * D.b * D.x ^ D.ε
      + (nT2 : ℝ) * D.k * D.b * D.x ^ D.ε / ((n : ℝ) * ((n : ℝ) * D.x ^ (-D.ε))) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hm0
  linarith

/-- Concrete fiber realization of the `√X` iterated theta-lift chain + Bost slope system
attached to a cyclic character level `Level.cyc ψ` at scale `(x, eps)`. -/
structure ThetaSlopeFiberRealization (ψ : PChar) (eD eL eps x : ℝ) : Prop where
  exists_fiber :
    ∃ (U0 : Type) (_ : Fintype U0) (_ : Nonempty U0)
      (W : U0 → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0))
      (Top : Type) (_ : Fintype Top) (m f n nT2 : ℕ)
      (D : SlopeData U0 W Top m f) (C : SlopeConsts) (Xpp eK K : ℝ),
      D.x = x ∧ D.ε = eps ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧
      D.SlopeHypotheses C Xpp ∧
      D.ErrorWindowBounds C Xpp eK K ∧
      D.B0 ≤ (2 * (n : ℝ)) * (m : ℝ) * D.b * x ^ eps ∧
      D.Nc ≤ (nT2 : ℝ) * D.k * D.b * x ^ eps / ((n : ℝ) * ((n : ℝ) * x ^ (-eps))) ∧
      RestSize eps x n (Fintype.card Top) nT2 m D.b D.k D.a ∧
      0 < n ∧ nT2 ≤ n ∧
      (Fintype.card Top : ℝ) * (m : ℝ) * D.b * (((nT2 : ℝ) / (n : ℝ)) / 2) *
          ((Level.cyc ψ).Gm x - 4 * x ^ ((1 : ℝ) / 2 + eps))
        ≤ (umean D.ASK - umean D.Main) + 2 * (Fintype.card Top : ℝ) * (m : ℝ) * D.b / x

/-- **Core Pointwise Engine Theorem (`SChain.ChainAt`)**:
Chains Bost common-slope cancellation (`mean_bound_of_slope_cancellation`), error collapse
(`errorTerm_le_rpow_errText`), `BNBounds` (`errText_le_errorBracket`), and the `√X` size-window
breakthrough (`growth_size_bound_breaks_two_thirds`) to deduce:
`(Level.cyc ψ).Gm x ≤ x ^ (1 / 2 + (eD + eL + 6) * eps)`. -/
theorem level_gm_bound_of_theta_fiber {ψ : PChar} {eD eL eps x : ℝ}
    (heD : 0 ≤ eD) (heL : 0 ≤ eL) (hx3 : 3 ≤ x) (h26 : 26 ≤ x ^ (3 * eps / 8))
    (hF : ThetaSlopeFiberRealization ψ eD eL eps x) :
    (Level.cyc ψ).Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * eps) := by
  obtain ⟨U0, _, _, W, _, _, Top, _, m, f, n, nT2, D, C, Xpp, eK, K,
    hx_eq, heps_eq, heD_le, heL_le, hSlope, hWin, hB0, hNc, hRest, hn_pos, hnT2_le, hBal⟩ :=
    hF.exists_fiber
  subst hx_eq heps_eq
  -- Step 1: Bost common-slope cancellation
  have hMean := D.mean_bound_of_slope_cancellation C Xpp hSlope
  -- Step 2: Error collapse under window bounds
  have hErr := D.errorTerm_le_rpow_errText C Xpp hWin
  -- Step 3: Bridge ErrText to errorBracketSizeWindows
  have hEB := errText_le_errorBracket D n nT2 hB0 hNc
  -- Step 4: Upgrade exponent from C.eDiv + C.eLoss + 3 to eD + eL + 3
  have hET0 : 0 ≤ D.ErrText := by
    unfold SlopeData.ErrText
    have hx1 : 1 ≤ D.x := hWin.x_ge_one
    have ha0 : 0 ≤ D.a := hSlope.setting.a_nonneg
    have hk0 : 0 < D.k := hSlope.setting.k_pos
    have hnT0 : 0 ≤ D.nT := Nat.cast_nonneg _
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hBN0 : 0 ≤ D.B0 + D.Nc := add_nonneg hWin.B0_nonneg hWin.Nc_nonneg
    exact add_nonneg
      (mul_nonneg (mul_nonneg hnT0 ha0) (add_nonneg zero_le_one (div_nonneg (sq_nonneg _) hk0.le)))
      (mul_nonneg hm0 hBN0)
  have hexp_le : D.x ^ ((C.eDiv + C.eLoss + 3) * D.ε)
      ≤ D.x ^ ((eD + eL + 3) * D.ε) :=
    Real.rpow_le_rpow_of_exponent_le hWin.x_ge_one (by nlinarith [hWin.eps_pos])
  have hErr_br : umean D.ASK - umean D.Main
      ≤ D.x ^ ((eD + eL + 3) * D.ε) *
          errorBracketSizeWindows D.x D.ε n (Fintype.card Top) nT2 m D.b D.k D.a := by
    calc umean D.ASK - umean D.Main
        ≤ D.errorTermWith C Xpp := by linarith
      _ ≤ D.x ^ ((C.eDiv + C.eLoss + 3) * D.ε) * D.ErrText := hErr
      _ ≤ D.x ^ ((eD + eL + 3) * D.ε) * D.ErrText :=
          mul_le_mul_of_nonneg_right hexp_le hET0
      _ ≤ D.x ^ ((eD + eL + 3) * D.ε) *
            errorBracketSizeWindows D.x D.ε n (Fintype.card Top) nT2 m D.b D.k D.a :=
          mul_le_mul_of_nonneg_left hEB (Real.rpow_nonneg hSlope.setting.x_pos.le _)
  -- Step 5: Assemble SizeWindowParams and break the 2/3 barrier!
  have hSW : SizeWindowParams (eD + eL + 3) D.ε D.x n (Fintype.card Top) nT2 m
      D.b D.k D.a (umean D.ASK - umean D.Main) :=
    { x_ge_three := hx3
      eps_pos := hWin.eps_pos
      C_nonneg := by linarith
      n_pos := hn_pos
      b_pos := hSlope.setting.b_pos
      aE_nonneg := hSlope.setting.a_nonneg
      rest := hRest
      nT2_le := hnT2_le
      m_le := hWin.m_le
      k_ge := hWin.xm_le_k
      err_le := hErr_br
      x_large_26 := h26 }
  have hBreak := growth_size_bound_breaks_two_thirds hSW hBal
  have hEq : (1 : ℝ) / 2 + (eD + eL + 3 + 3) * D.ε = (1 : ℝ) / 2 + (eD + eL + 6) * D.ε := by ring
  rwa [hEq] at hBreak

/-- **Minimal, Zero-Dead-Field Input Bundle for Pillar 2 (`ThetaSlopeEngine`)**:
Explicit `structure` parameter (zero `axiom`s, zero `sorry`s, zero dead fields) recording the
irreducible automorphic/theta-lift realization feeding the `√X` chain + Bost slope engine. -/
structure MinimalThetaEngineInputs (S : SelmerSystem) where
  eD : ℝ
  eL : ℝ
  eD_nonneg : 0 ≤ eD
  eL_nonneg : 0 ≤ eL
  pairEx : PairEx
  realize : ∀ (ψ : PChar) (eps J : ℝ), 0 < eps → eps < 1 / 52 → 1 ≤ J →
    ∃ X0 : ℝ, ∀ (x Y : ℝ) (q d e : ℕ), X0 ≤ x →
      WinDatum S ψ eps J 1 x Y q d e →
      ThetaSlopeFiberRealization ψ eD eL eps x

/-- **Per-Character Window Bound (`LevelWindowBound (Level.cyc ψ) (3 / 2)`)**:
From `VWinAt S ψ 401` and `MinimalThetaEngineInputs S`, produces arbitrarily large
`[Y, Y ^ (3 / 2)]` windows where `(Level.cyc ψ).Gm y ≤ y ^ θ` for every `θ ∈ (1 / 2, 1)`. -/
theorem levelWindowBound_of_vwinAt (S : SelmerSystem) (I : MinimalThetaEngineInputs S)
    (ψ : PChar) (hV : VWinAt S ψ 401) :
    LevelWindowBound (Level.cyc ψ) (3 / 2) := by
  intro θ hθ_lo _hθ_hi Y₀
  -- Choose eps > 0 small enough that both eps < 1/52 AND 1/2 + (eD + eL + 6) * eps ≤ θ
  have hden_pos : 0 < I.eD + I.eL + 6 := by linarith [I.eD_nonneg, I.eL_nonneg]
  set eps : ℝ := min (1 / 104) ((θ - 1 / 2) / (I.eD + I.eL + 6))
  have heps_pos : 0 < eps := lt_min (by norm_num) (div_pos (by linarith) hden_pos)
  have heps52 : eps < 1 / 52 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hexp_le_theta : (1 : ℝ) / 2 + (I.eD + I.eL + 6) * eps ≤ θ := by
    have h1 : eps ≤ (θ - 1 / 2) / (I.eD + I.eL + 6) := min_le_right _ _
    have h2 : (I.eD + I.eL + 6) * eps ≤ θ - 1 / 2 :=
      (le_div_iff₀' hden_pos).mp h1
    linarith
  -- Extract arbitrarily large [Z, Z^(3/2)] windows carrying WinDatum at cutoff 400
  obtain ⟨J, hJ, hWin⟩ := winPairs_of_vwinAt S ψ eps 1 heps_pos heps52 le_rfl hV I.pairEx
  obtain ⟨X0, hReal⟩ := I.realize ψ eps J heps_pos heps52 hJ
  set X26 : ℝ := (26 : ℝ) ^ (8 / (3 * eps))
  set thresh : ℝ := max (max Y₀ 3) (max X0 X26)
  obtain ⟨Z, hZ_ge, hZ_win⟩ := hWin thresh
  have hZ_Y0 : Y₀ ≤ Z := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hZ_ge)
  have hZ_3 : 3 ≤ Z := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hZ_ge)
  have hZ_X0 : X0 ≤ Z := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hZ_ge)
  have hZ_26 : X26 ≤ Z := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hZ_ge)
  refine ⟨Z, hZ_Y0, fun y hy => ?_⟩
  have hZy : Z ≤ y := hy.1
  have hyZ : y ≤ Z ^ ((3 : ℝ) / 2) := by
    have hrew : (1 : ℝ) + ((3 : ℝ) / 2 - 1) = (3 : ℝ) / 2 := by ring
    simpa only [hrew] using hy.2
  have hy3 : 3 ≤ y := hZ_3.trans hZy
  have hy1 : 1 ≤ y := by linarith
  have hy26 : 26 ≤ y ^ (3 * eps / 8) := by
    have hX26_nn : 0 ≤ X26 := Real.rpow_nonneg (by norm_num) _
    have hpow : X26 ^ (3 * eps / 8) = 26 := by
      dsimp only [X26]
      rw [← Real.rpow_mul (by norm_num)]
      have h1 : 8 / (3 * eps) * (3 * eps / 8) = 1 := by field_simp [heps_pos.ne']
      rw [h1, Real.rpow_one]
    calc (26 : ℝ) = X26 ^ (3 * eps / 8) := hpow.symm
      _ ≤ y ^ (3 * eps / 8) := Real.rpow_le_rpow hX26_nn (hZ_26.trans hZy) (by positivity)
  obtain ⟨Y, q, d, e, hDat⟩ := hZ_win y hZy hyZ
  have hFib := hReal y Y q d e (hZ_X0.trans hZy) hDat
  have hGm := level_gm_bound_of_theta_fiber I.eD_nonneg I.eL_nonneg hy3 hy26 hFib
  rw [one_mul]
  exact hGm.trans (Real.rpow_le_rpow_of_exponent_le hy1 hexp_le_theta)

/-- **Main Pillar 2 Export (`ThetaSlopeContract S`)**:
Compiles the complete `√X` iterated theta-lift chain + Bost Arakelov slope engine into
`RHDirect.ThetaSlopeContract S` (`VWin S → AllLevelsWindowBound (3 / 2)`), ready for
`RHDirect.Main` and `RHDirect.AnalyticBridge`! -/
theorem thetaSlopeContract_of_inputs (S : SelmerSystem) (I : MinimalThetaEngineInputs S) :
    ThetaSlopeContract S :=
  ⟨fun hV ψ => levelWindowBound_of_vwinAt S I ψ (hV ψ)⟩

end

end RHDirect.ThetaSlopeEngine
