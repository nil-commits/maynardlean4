import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# RHDirect.Interfaces

Clean, dead-field-free Lean 4 interface contracts for the from-scratch compact rebuild of
the Generalized Riemann Hypothesis / Riemann Hypothesis proof (`rh-direct`).

This file defines ONLY:
1. The exact upstream headline statements (`Statements.lean` verbatim + Mathlib's `RiemannHypothesis`).
2. Unified analytic core objects (`PChar`, `ramp`, `Gchi`, `Gz`, `CharFamily`, `Level`, `CosetFrame`),
   collapsing four redundant copies in the original archive into one canonical specification.
3. The Selmer / Vandiver window (`VWin`, `VWinAt`, `VVle`, `WinPair`, `PageN`, `IsChiField`) boundary
   between Pillar 3 (`GaloisModularityCore`) and Pillar 2 (`ThetaSlopeEngine`).
4. The iterated theta-lift chain and Bost Arakelov slope parameters (`ScaleParams`, `ChainRanks`,
   `RestSize`, `errorBracketSizeWindows`, `BostSlopeConfig`) for Pillar 2 (`ThetaSlopeEngine`).
5. Minimal, zero-dead-field pillar contracts (`AnalyticBridgeContract`, `ThetaSlopeContract`,
   `GaloisModularityContract`, `RHDirectAssembly`).

Zero `sorry`, zero custom `axiom`s.
-/

/-! ## 0. Exact Upstream Headline Statements (`src/Statements.lean` verbatim) -/

def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

noncomputable section

open scoped ArithmeticFunction.vonMangoldt
open Complex NumberField

namespace RHDirect

/-! ## 1. Unified Primitive Characters, Cesàro von Mangoldt Sums & Levels -/

/-- A primitive Dirichlet character of conductor `N`. -/
structure PChar where
  N : ℕ
  [ne : NeZero N]
  χ : DirichletCharacter ℂ N
  prim : χ.IsPrimitive

attribute [instance] PChar.ne

namespace PChar

def val (ψ : PChar) (a : ℕ) : ℂ := ψ.χ (a : ZMod ψ.N)

def one : PChar := ⟨1, 1, DirichletCharacter.isPrimitive_one_level_one⟩

def inv (ψ : PChar) : PChar :=
  ⟨ψ.N, ψ.χ⁻¹, by
    have h : ψ.χ.conductor = ψ.N := ψ.prim
    exact (DirichletCharacter.conductor_inv ψ.χ).trans h⟩

theorem inv_inv (ψ : PChar) : ψ.inv.inv = ψ := by
  cases ψ
  simp only [inv]
  congr 1
  exact _root_.inv_inv _

def of {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : PChar :=
  @PChar.mk χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter χ.primitiveCharacter_isPrimitive

def IsReal (ψ : PChar) : Prop := ∀ a : ZMod ψ.N, (ψ.χ a).im = 0

def ZeroFreeAbove (ψ : PChar) (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction ψ.χ s ≠ 0

private theorem mk_eq_of_changeLevel_eq_self {N d : ℕ} [NeZero N] [NeZero d]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ d)
    (hd : d ∣ N) (hc : DirichletCharacter.changeLevel hd ψ = χ)
    (h1 : ψ.IsPrimitive) (h2 : χ.IsPrimitive) (he : d = N) :
    PChar.mk d ψ h1 = PChar.mk N χ h2 := by
  subst he
  rw [DirichletCharacter.changeLevel_self] at hc
  subst hc
  rfl

theorem of_self (ψ : PChar) : PChar.of ψ.χ = ψ := by
  have : NeZero ψ.χ.conductor := ⟨ψ.χ.conductor_ne_zero⟩
  exact mk_eq_of_changeLevel_eq_self ψ.χ ψ.χ.primitiveCharacter ψ.χ.conductor_dvd_level
    ψ.χ.changeLevel_primitiveCharacter ψ.χ.primitiveCharacter_isPrimitive ψ.prim ψ.prim

private theorem mk_eq_one_of_level_eq_one {d : ℕ} [NeZero d]
    (ψ : DirichletCharacter ℂ d) (h : ψ.IsPrimitive) (he : d = 1) :
    PChar.mk d ψ h = PChar.one := by
  subst he
  obtain rfl := DirichletCharacter.level_one ψ
  rfl

theorem of_one (M : ℕ) [NeZero M] : PChar.of (1 : DirichletCharacter ℂ M) = PChar.one := by
  have : NeZero (1 : DirichletCharacter ℂ M).conductor :=
    ⟨(1 : DirichletCharacter ℂ M).conductor_ne_zero⟩
  exact mk_eq_one_of_level_eq_one _ _ DirichletCharacter.conductor_one

private theorem mk_eq_of_changeLevel_eq {M d e : ℕ} [NeZero M] [NeZero d] [NeZero e]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ d) (φ : DirichletCharacter ℂ e)
    (hd : d ∣ M) (he' : e ∣ M) (hde : d = e)
    (hψ : DirichletCharacter.changeLevel hd ψ = χ)
    (hφ : DirichletCharacter.changeLevel he' φ = χ)
    (p1 : ψ.IsPrimitive) (p2 : φ.IsPrimitive) :
    PChar.mk d ψ p1 = PChar.mk e φ p2 := by
  subst hde
  have hq : ψ = φ := DirichletCharacter.changeLevel_injective hd (hψ.trans hφ.symm)
  subst hq
  rfl

theorem of_inv {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) :
    PChar.of χ⁻¹ = (PChar.of χ).inv := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have : NeZero χ⁻¹.conductor := ⟨χ⁻¹.conductor_ne_zero⟩
  exact mk_eq_of_changeLevel_eq χ⁻¹ χ⁻¹.primitiveCharacter χ.primitiveCharacter⁻¹
    χ⁻¹.conductor_dvd_level χ.conductor_dvd_level (DirichletCharacter.conductor_inv χ)
    χ⁻¹.changeLevel_primitiveCharacter
    (by rw [map_inv, DirichletCharacter.changeLevel_primitiveCharacter]) _ _

end PChar

/-- Nonvanishing of `L(ψ, s)` for all primitive Dirichlet characters `ψ` and `Re(s) > 1/2`. -/
def ZeroFreeAll : Prop := ∀ ψ : PChar, ψ.ZeroFreeAbove (1 / 2)

/-- Riesz/Cesàro-1 weighted von Mangoldt sum `∑_{n ≤ y} Λ(n) f(n) (y/n - 1)_+`. -/
def ramp (f : ℕ → ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊y⌋₊ + 1), (Λ n : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ)

open Classical in
/-- Subtracted Cesàro von Mangoldt functional for a Dirichlet character `χ`. -/
def Gchi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  if χ = 1 then
    ramp (fun n => χ n) y - ((y * Real.log y : ℝ) : ℂ) +
      (((1 + Real.eulerMascheroniConstant) * y : ℝ) : ℂ)
  else
    ramp (fun n => χ n) y +
      (y : ℂ) * (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)

/-- Subtracted Cesàro von Mangoldt functional for `ζ(s)`. -/
def Gz (y : ℝ) : ℝ :=
  (ramp (fun _ => 1) y).re - y * Real.log y + (1 + Real.eulerMascheroniConstant) * y

/-- A finite positively weighted family of Dirichlet characters for the windowed Landau criterion. -/
structure CharFamily where
  ι : Type
  [fin : Fintype ι]
  N : ι → ℕ
  [nz : ∀ i, NeZero (N i)]
  χ : ∀ i, DirichletCharacter ℂ (N i)
  a : ι → ℝ
  a_pos : ∀ i, 0 < a i
  adm : ∀ i, N i = 1 ∨ χ i ≠ 1

attribute [instance] CharFamily.fin CharFamily.nz

namespace CharFamily

def Gm (F : CharFamily) (y : ℝ) : ℝ := ∑ i, F.a i * (Gchi (F.χ i) y).re

def ZeroFree (F : CharFamily) (θ : ℝ) : Prop :=
  ∀ i, ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction (F.χ i) s ≠ 0

def WindowHyp (F : CharFamily) (θ δ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∃ R : ℝ → ℝ,
    MeasureTheory.IntegrableOn (fun y => R y * y ^ (-θ - 1)) (Set.Icc Y (Y ^ (1 + δ))) ∧
    (∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), 0 ≤ R y ∧ F.Gm y ≤ R y) ∧
    ∫ y in Set.Icc Y (Y ^ (1 + δ)), R y * y ^ (-θ - 1) ≤ Y ^ η

end CharFamily

/-- `g` satisfies `g y ≤ C * y ^ θ` on arbitrarily large multiplicative windows `[Y, Y^(1+δ)]`. -/
def HasRpowWindow (g : ℝ → ℝ) (θ δ C : ℝ) : Prop :=
  ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), g y ≤ C * y ^ θ

/-- `W` contains arbitrarily large multiplicative windows `[Y, Y^la]`. -/
def HasWindows (W : Set ℝ) (la : ℝ) : Prop :=
  ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ Set.Icc Y (Y ^ la) ⊆ W

/-- A finite inverse-closed level of primitive Dirichlet characters with `(3o + 1)⁻¹` coset weights. -/
structure Level where
  KEPT : Finset PChar
  one_mem : PChar.one ∈ KEPT
  inv_mem : ∀ ψ ∈ KEPT, ψ.inv ∈ KEPT
  o : ℕ
  o_pos : 0 < o

namespace Level

variable (L : Level)

def ZeroFreeAbove (θ : ℝ) : Prop := ∀ ψ ∈ L.KEPT, ψ.ZeroFreeAbove θ

def ZeroFreeLevel : Prop := L.ZeroFreeAbove (1 / 2)

open Classical in
def Nt : Finset PChar := L.KEPT.erase PChar.one

def wt (_ψ : PChar) : ℝ := (3 * (L.o : ℝ) + 1)⁻¹

open Classical in
def Gm (y : ℝ) : ℝ := Gz y + ∑ ψ ∈ L.Nt, L.wt ψ * (Gchi ψ.χ y).re

open Classical in
def ofSub {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) : Level where
  KEPT := (Finset.univ.filter fun χ : DirichletCharacter ℂ M => χ ∈ Ξ).image PChar.of
  one_mem :=
    Finset.mem_image.2 ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, Ξ.one_mem⟩, PChar.of_one M⟩
  inv_mem := by
    intro ψ h
    obtain ⟨χ, h1, rfl⟩ := Finset.mem_image.1 h
    exact Finset.mem_image.2
      ⟨χ⁻¹, Finset.mem_filter.2 ⟨Finset.mem_univ _, Ξ.inv_mem (Finset.mem_filter.1 h1).2⟩,
        PChar.of_inv χ⟩
  o := Nat.card Ξ
  o_pos := Nat.card_pos_iff.2 ⟨⟨1, Ξ.one_mem⟩, Finite.of_fintype _⟩

theorem mem_ofSub {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (ψ : PChar) :
    ψ ∈ (Level.ofSub Ξ).KEPT ↔ ∃ χ ∈ Ξ, PChar.of χ = ψ := by
  classical
  simp [Level.ofSub]

def cyc (ψ : PChar) : Level := Level.ofSub (Subgroup.zpowers ψ.χ)

theorem mem_cyc (ψ : PChar) : ψ ∈ (Level.cyc ψ).KEPT :=
  (mem_ofSub _ _).2 ⟨ψ.χ, Subgroup.mem_zpowers _, ψ.of_self⟩

end Level

/-- Windowed Cesàro von Mangoldt upper bound at exponent `la` (`la = 3/2`) for a level `L`. -/
def LevelWindowBound (L : Level) (la : ℝ) : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → HasRpowWindow L.Gm θ (la - 1) 1

/-- Windowed Cesàro von Mangoldt upper bound for every cyclic character level `Level.cyc ψ`. -/
def AllLevelsWindowBound (la : ℝ) : Prop :=
  ∀ ψ : PChar, LevelWindowBound (Level.cyc ψ) la

/-- Finite abelian coset frame `(A, A0)` of index `o` with `(4, 3)/(3o + 1)` coset density
used in finite abelian Fourier inversion (`TopsSum`). -/
structure CosetFrame where
  A : Type
  [addCommGroup : AddCommGroup A]
  [fintype : Fintype A]
  [decEq : DecidableEq A]
  A0 : AddSubgroup A
  [decMem : DecidablePred (· ∈ A0)]
  o : ℕ
  o_pos : 0 < o
  index_eq : o * Fintype.card A0 = Fintype.card A

attribute [instance] CosetFrame.addCommGroup CosetFrame.fintype CosetFrame.decEq CosetFrame.decMem

namespace CosetFrame

variable (φ : CosetFrame)

def lam (γ : φ.A) : ℝ :=
  (if γ ∈ φ.A0 then (4 : ℝ) else 3) / (3 * (φ.o : ℝ) + 1)

def Shares (TT : Finset φ.A) (δ : ℝ) : Prop :=
  ∀ γ : φ.A,
    |((TT.filter fun t => t - γ ∈ φ.A0).card : ℝ) - φ.lam γ * (TT.card : ℝ)| ≤ δ * (TT.card : ℝ)

end CosetFrame

/-! ## 2. Selmer / Vandiver Window (`VWin`) Interface (Pillar 3 ↔ Pillar 2) -/

/-- Abstract Selmer / Shafarevich–Tate length system over number fields `E`,
recording `shaLen E l e ∈ ℕ∞` for prime `l` and twist weight `e : ℕ`. -/
structure SelmerSystem where
  shaLen : (E : Type) → [Field E] → [NumberField E] → Nat.Primes → ℕ → ℕ∞

/-- Bounded weighted sum of Selmer/Sha lengths over all primes `l` and weights `1 ≤ e < t`. -/
def VVle (S : SelmerSystem) (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) : Prop :=
  (∀ (l : Nat.Primes) (e : ℕ), 0 < e → e < t → S.shaLen E l e ≠ ⊤) ∧
  ∀ P : Finset Nat.Primes,
    ∑ l ∈ P, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E l e).toNat : ℝ) ≤ B

theorem VVle.mono {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {t t' : ℕ} {B B' : ℝ} (h : VVle S E t B) (ht : t' ≤ t) (hB : B ≤ B') :
    VVle S E t' B' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun l e he1 he2 => h1 l e he1 (lt_of_lt_of_le he2 ht), fun P => ?_⟩
  refine le_trans ?_ (le_trans (h2 P) hB)
  apply Finset.sum_le_sum
  intro l _
  apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg _)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    simp only [Finset.mem_Ico] at he ⊢
    omega
  · intro e _ _
    positivity

/-- The abelian CM host field `E` attached to `(ψ, e, q, d)` inside `ℚ(ζ_N)`. -/
def IsChiField (ψ : PChar) (e q d : ℕ) (E : Type) [Field E] [NumberField E] : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (j : E →ₐ[ℚ] CyclotomicField N ℚ) (ζ : CyclotomicField N ℚ),
    2 ^ (e + 2) ∣ N ∧ ψ.N ∣ N ∧ q ∣ N ∧ d ∣ N ∧ IsPrimitiveRoot ζ N ∧
    ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ), τ ζ = ζ ^ a →
      ((∀ x : E, τ (j x) = j x) ↔
        (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ ψ.val a = 1 ∧
          jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1)

/-- Admissible auxiliary prime pair `(q, d)` at window scale `Y` and exponent `eps`. -/
structure WinPair (eps Y : ℝ) (q d : ℕ) : Prop where
  q_prime : q.Prime
  q_mod : q % 8 = 3
  q_lo : Y ^ (eps / 5) / 2 < Real.log q
  q_up : Real.log q ≤ Y ^ (eps / 5)
  d_prime : d.Prime
  d_mod : d % 16 = 7
  d_lo : Y ^ (eps / 5) * Real.log Y ^ 2 / 2 < Real.log d
  d_up : Real.log d ≤ Y ^ (eps / 5) * Real.log Y ^ 2
  d_q : q ∣ d + 1
  d_small : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ Y ^ (eps / 5) → p ∣ d + 1

/-- Iwasawa 2-tower page height `2^e ∈ [x^(2+8ε), 2 x^(2+8ε)]`. -/
def PageN (eps x : ℝ) (e : ℕ) : Prop :=
  x ^ (2 + 8 * eps) ≤ (2 : ℝ) ^ e ∧ (2 : ℝ) ^ e ≤ 2 * x ^ (2 + 8 * eps)

theorem exists_pageN (eps : ℝ) (he : 0 < eps) : ∃ e : ℝ → ℕ, ∀ x ≥ (1 : ℝ), PageN eps x (e x) := by
  have : ∀ x : ℝ, ∃ e : ℕ, x ≥ 1 → PageN eps x e := by
    intro x
    by_cases hx : x ≥ 1
    · have h1 : (1 : ℝ) ≤ x ^ (2 + 8 * eps) := Real.one_le_rpow hx (by linarith)
      obtain ⟨n, a, b⟩ := exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)
      refine ⟨n + 1, fun _ => ⟨b.le, ?_⟩⟩
      rw [pow_succ]
      linarith
    · exact ⟨0, fun h => absurd h hx⟩
  choose e he using this
  exact ⟨e, he⟩

/-- Pointwise Selmer/Vandiver bound at scale `x` with cutoff `⌊x ^ Ct⌋₊`. -/
def VAt (S : SelmerSystem) (ψ : PChar) (eps Ct : ℝ) (q d e : ℕ) (x : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E],
    IsChiField ψ e q d E → VVle S E ⌊x ^ Ct⌋₊ (Real.sqrt (Real.exp (x ^ eps)))

/-- Windowed Selmer/Vandiver bound at cutoff exponent `Ct` (`Ct = 401`). -/
def VWinAt (S : SelmerSystem) (ψ : PChar) (Ct : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 →
    ∀ e : ℝ → ℕ, (∀ x ≥ (1 : ℝ), PageN eps x (e x)) →
      ∃ J : ℝ, 1 ≤ J ∧ ∃ X0 : ℝ, ∀ X ≥ X0, ∀ q d : ℕ, WinPair eps (X ^ (1 / J)) q d →
        ∃ Y : ℝ, X ^ (1 / J) ≤ Y ∧ Y ^ (2 : ℝ) ≤ X ∧
          ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → VAt S ψ eps Ct q d (e x) x

/-- Full Selmer/Vandiver window property `VWin := ∀ ψ, VWinAt S ψ 401`. -/
def VWin (S : SelmerSystem) : Prop := ∀ ψ : PChar, VWinAt S ψ 401

/-! ## 3. Iterated Theta-Lift Chain & Bost Slope Calculus Parameters (Pillar 2) -/

/-- Scale parameters for the `√x`-length iterated theta-lift chain. -/
structure ScaleParams where
  x : ℝ
  eps : ℝ
  delta1 : ℝ
  L : ℝ
  x_gt_one : 1 < x
  eps_pos : 0 < eps
  eps_lt : eps < 1 / 52
  delta1_pos : 0 < delta1
  L_pos : 0 < L

/-- Unitary group rank parameters along the `m`-step chain `U(X_0) → ... → U(X_m)`
with `N(j) = k + j * (t + 1)`. -/
structure ChainRanks where
  n : ℕ
  f : ℕ
  r : ℕ
  k : ℕ
  m : ℕ
  t : ℕ

def ChainRanks.chainRank (R : ChainRanks) (j : ℕ) : ℕ := R.k + j * (R.t + 1)

/-- `377 = 1 + 47 * 8` orbital/test-vector multiplicity threshold. -/
def TOv (s : ScaleParams) : ℕ := ⌈s.x ^ (377 : ℝ)⌉₊

/-- Wave-grid multiplicity factor `nWv` entering the rank balance `r + t = 8 f r + 4 + TOv * nWv`. -/
def nWv (R : ChainRanks) (s : ScaleParams) : ℕ :=
  8 * ⌈10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8⌉₊

/-- Exact asymptotic rank-scale envelope `RankVal` pinning `R.t ≤ x ^ 400` for `eps < 1 / 52`. -/
def RankVal (s : ScaleParams) (R : ChainRanks) : Prop :=
  (s.x ^ (2 + 8 * s.eps) ≤ (R.n : ℝ) ∧ (R.n : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps)) ∧
  (Real.sqrt (s.x * s.delta1) ≤ (R.m : ℝ) ∧ (R.m : ℝ) ≤ 2 * Real.sqrt (s.x * s.delta1)) ∧
  (s.x ^ (9 / 2 + 10 * s.eps) ≤ (R.k : ℝ) ∧ (R.k : ℝ) ≤ 2 * s.x ^ (9 / 2 + 10 * s.eps)) ∧
  R.r + R.t = 8 * R.f * R.r + 4 + TOv s * nWv R s

/-- Chain-size envelope `RestSize` forcing `m ≥ x^(1/2 - ε)` (`SChain.lean`). -/
def RestSize (ε x : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ) : Prop :=
  aE ≤ 2 * x * b ∧
  x ^ (-(ε / 8)) * n / 2 ≤ nT ∧
  x ^ (-ε) ≤ (nT2 : ℝ) / n ∧
  x ^ ((1 : ℝ) / 2 - ε) ≤ m ∧
  k ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε)

/-- Exact slope-cancellation error bracket (`ErrorFormsWeakWindowsFalse.lean`). -/
def errorBracketSizeWindows (x ε : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ) : ℝ :=
  (nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k) +
    (m : ℝ) * ((2 * (n : ℝ)) * (m : ℝ) * b * x ^ ε +
      (nT2 : ℝ) * k * b * x ^ ε / ((n : ℝ) * ((n : ℝ) * x ^ (-ε))))

/-- Abstract Bost Arakelov slope inequality data at a single fiber `u0`. -/
structure BostSlopeFiber where
  del : ℝ
  η : ℝ
  e : ℝ
  s : ℝ
  muMinCC : ℝ
  muCC : ℝ
  HH : ℝ
  uF : ℝ
  cardW : ℕ

/-- The Bost slope inequality (`MeanBoundSecondForm.lean`). -/
def BostSlopeFiber.SlopeIneq (B : BostSlopeFiber) : Prop :=
  0 ≤ B.del → B.del < 1 → 0 ≤ B.η → 0 ≤ B.e → B.e ≤ 1 / 4 →
    B.s - B.muMinCC ≤ B.HH → 0 < B.HH →
      B.s - Real.log (B.cardW : ℝ) -
        (1 - B.del)⁻¹ * (4 * B.uF * Real.log (1 + B.HH / B.uF) +
          (B.η + 4 * Real.sqrt B.e) * B.HH) ≤ B.muCC

/-! ## 4. Clean, Dead-Field-Free Pillar Contracts -/

/-- Pillar 1 contract (`RHDirect.AnalyticBridge` + `RHDirect.LandauWindow`):
windowed Cesàro von Mangoldt bounds at any exponent `la > 1` imply `ZeroFreeAll`. -/
structure AnalyticBridgeContract : Prop where
  zeroFreeAll_of_windows : ∀ la : ℝ, 1 < la → AllLevelsWindowBound la → ZeroFreeAll

/-- Pillar 2 contract (`RHDirect.ThetaSlopeEngine` + `RHDirect.SlopeInequality`):
the Selmer/Vandiver window `VWin S` feeds the `√x` iterated theta-lift chain and Bost slope
engine to produce `AllLevelsWindowBound (3 / 2)`. -/
structure ThetaSlopeContract (S : SelmerSystem) : Prop where
  windows_of_vwin : VWin S → AllLevelsWindowBound (3 / 2)

/-- Pillar 3 contract (`RHDirect.GaloisModularityCore` + `RHDirect.AutomorphicInputs`):
minimal dead-field-free Galois/Local-Langlands/automorphy inputs produce `VWin S`. -/
structure GaloisModularityContract (S : SelmerSystem) : Prop where
  vwin : VWin S

/-- Complete three-pillar assembly contract (zero dead fields, zero axioms). -/
structure RHDirectAssembly (S : SelmerSystem) : Prop where
  galois : GaloisModularityContract S
  theta : ThetaSlopeContract S
  analytic : AnalyticBridgeContract

end RHDirect

end
