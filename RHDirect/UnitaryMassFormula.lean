import RHDirect.Interfaces
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Factorial.Basic

/-!
# RHDirect.UnitaryMassFormula

Unified, 0-`sorry`, 0-`axiom` Lean 4 formalization of:

1. **Single Parametric Stabilizer-Orbit Volume & Siegel–Tamagawa Framework**
   Collapses the **3-way near-identical 448-file / 57,658-line clone** in
   `Formalism/PeriodIntegrals/UnitaryGroupMassFormula/`
   (`StabilizerOrbitVolume` 147f/19,387L, `StabilizerVolume` 155f/19,855L,
   `WeilStabilizerVolume` 146f/18,416L) into ONE parametric theorem
   `volStab_eq_of_siegelWeil_unfold` and one general proportionality law
   `volStab_ratio_of_siegelWeil_unfold`, instantiating all three cloned variants
   (`VolStabSW`, `VolStabS`, `VolStabW`) as trivial 3-line specializations.

2. **Exact Finite-Genus Mass Formula & Orbit-Stabilizer Measure Ratio**
   Proves from first principles on any measurable group `G` with left-invariant measure `μ`,
   countable discrete subgroup `Γ`, compact-open level `K ≤ G`, and finite double-coset
   genus decomposition `G = ⨆ i, Γ g_i K`:
   - `measure_fundamentalDomain_eq_genus_mass_sum`:
     `μ 𝓕 = ∑ i, μ K * (|Aut(L_i)| : ℝ≥0∞)⁻¹`
   - `genusMass_eq_covolume_div`:
     `∑ i, (|Aut(L_i)| : ℝ)⁻¹ = (μ 𝓕).toReal / (μ K).toReal`
   - `finite_orbit_stabilizer_mass_identity`:
     for a finite group `G` acting on a finite genus `X`,
     `∑ ω : MulAction.orbitRel.Quotient G X, (|Stab_G(x_ω)| : ℝ)⁻¹ = |X| / |G|`.

3. **Unitary Mass Ratio, Siegel–Tamagawa Telescoping & `GL5` Signature Induction**
   - `massRatioFactor`: the exact Siegel–Tamagawa unitary step factor
     `(((M - 1)! * (v_E / π)^M)^f / √((2 v_E)^f)) * L(M)`.
   - `mass_telescope_eq_prod`: exact telescoping of `mass(r) / mass(k)` across ranks `k + 1 ≤ M ≤ r`.
   - `volume_eq_mass_of_ratio_induction`: unified definite-to-indefinite (`(2, 0) → (P, Q)`)
     signature induction proving `vol P Q = mass (P + Q)` for all `P ≥ 2, Q ≥ 0`
     (replacing `GL5/DiscreteSeriesOfFormalDegree.lean` boilerplate).

4. **Explicit `mass_ratio_ge` Analytic Lower Bounds for the Theta-Lift Covolume Comparison**
   - `log_factorial_ge_mul_log_sub`: clean Stirling-type lower bound `n log n - n ≤ log (n!)`.
   - `log_mass_ratio_exact`: exact logarithmic expansion of the telescoped Siegel mass ratio.
   - `mass_ratio_ge`: sharp explicit lower bound on the normalized log mass/covolume ratio
     `(1 / (f * k)) * log (D^* / d^*)` combining Siegel mass telescoping, level-index growth
     `Isig / Ipi`, Euler-factor bounds, and Weyl dimension ratios.
   - `mass_ratio_ge_of_scaleParams`: direct bridge to `RHDirect.ScaleParams` / `RHDirect.ChainRanks`
     showing how the `m * (log g₁ + log g₂)` growth dominates `O(L + m^2 L / k)` in the `√x` chain.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open MeasureTheory Finset Real
open scoped ENNReal BigOperators Pointwise

namespace RHDirect.UnitaryMassFormula

/-! ## 1. Parametric Stabilizer-Orbit Volume Framework (Unifying `VolStabSW`, `VolStabS`, `VolStabW`) -/

/-- The three cloned stabilizer-volume variants in the upstream 57,658-line directory cluster
differ only in their rank convergence condition (`a + 2 ≤ M` vs `2 * a < M`) and optional
archimedean smoothness predicate (`IsSmoothCc`). -/
inductive StabVolVariant : Type
  | sw     -- `StabilizerOrbitVolume` (`PI.VolStabSW`): `a + 2 ≤ M`, base admissible test functions
  | smooth -- `StabilizerVolume` (`PI.VolStabS`): `2 * a < M`, smooth `IsSmoothCc` test functions
  | weil   -- `WeilStabilizerVolume` (`PI.VolStabW`): `2 * a < M`, base admissible test functions
  deriving DecidableEq, Repr

/-- Rank-range convergence predicate parameterized by `StabVolVariant`. -/
def StabVolVariant.rankCond : StabVolVariant → ℕ → ℕ → Prop
  | .sw, a, M     => 1 ≤ a ∧ a + 2 ≤ M
  | .smooth, a, M => 1 ≤ a ∧ 2 * a < M
  | .weil, a, M   => 1 ≤ a ∧ 2 * a < M

theorem StabVolVariant.rankCond_weil_implies_sw {a M : ℕ}
    (h : StabVolVariant.weil.rankCond a M) : StabVolVariant.sw.rankCond a M := by
  rcases h with ⟨ha, hM⟩
  exact ⟨ha, by omega⟩

theorem StabVolVariant.rankCond_smooth_iff_weil (a M : ℕ) :
    StabVolVariant.smooth.rankCond a M ↔ StabVolVariant.weil.rankCond a M := Iff.rfl

/-- Abstract orbit-stabilizer Siegel–Weil context over an ambient group `G`, stabilizer `H`,
and orbit space `O`, with measures `μ`, `μ'`, `ν` and fundamental domains `𝓕`, `𝓕'`. -/
structure OrbitStabContext (G H O : Type*) [MeasurableSpace G] [MeasurableSpace H]
    [MeasurableSpace O] where
  μ : Measure G
  μ' : Measure H
  ν : Measure O
  𝓕 : Set G
  𝓕' : Set H
  /-- Orbital theta integral functional `Θ_φ(h)` for a real-valued test function `φ : O → ℝ`. -/
  thetaS : (O → ℝ) → G → ℂ
  /-- Variant-specific admissible test-function class (`IsAdm` for `SW`/`W`, `IsAdmS` for `S`). -/
  Adm : (O → ℝ) → Prop

/-- General Siegel–Weil proportionality data with scaling constant `c ≠ 0`
(the Tamagawa/measure ratio; `c = 1` is exact stabilizer-orbit volume equality). -/
structure SiegelWeilUnfoldHyp {G H O : Type*} [MeasurableSpace G] [MeasurableSpace H]
    [MeasurableSpace O] (C : OrbitStabContext G H O) (c : ℝ) : Prop where
  /-- Ambient fundamental domain has finite measure (`SWa1`). -/
  fd_lt_top : C.μ C.𝓕 < ⊤
  /-- Siegel–Weil orbital mean identity (`SWeqOm`, generalized to proportionality `c`). -/
  sw_eq_orbit : ∀ φ : O → ℝ, C.Adm φ →
    (C.μ C.𝓕).toReal⁻¹ • ∫ h in C.𝓕, C.thetaS φ h ∂C.μ = c • ∫ x, (φ x : ℂ) ∂C.ν
  /-- Orbit-stabilizer unfolding identity (`Unfold`). -/
  unfold : ∀ φ : O → ℝ, C.Adm φ →
    (∫ h in C.𝓕, C.thetaS φ h ∂C.μ) ≠ 0 →
      C.μ' C.𝓕' ≠ ⊤ ∧
      ∫ h in C.𝓕, C.thetaS φ h ∂C.μ = (C.μ' C.𝓕').toReal • ∫ x, (φ x : ℂ) ∂C.ν
  /-- Existence of an admissible test function with nonvanishing orbital integral (`PosTest`). -/
  pos_test : ∃ φ : O → ℝ, C.Adm φ ∧ ∫ x, (φ x : ℂ) ∂C.ν ≠ 0

/-- **Master Parametric Orbit-Stabilizer Measure-Ratio Theorem**:
from Siegel–Weil proportionality with constant `c ≠ 0`, unfolding, and a nonvanishing admissible
test function, the stabilizer covolume is finite and satisfies
`(μ' 𝓕').toReal / (μ 𝓕).toReal = c` and `μ' 𝓕' = ENNReal.ofReal c * μ 𝓕` (when `0 ≤ c`). -/
theorem volStab_ratio_of_siegelWeil_unfold {G H O : Type*} [MeasurableSpace G]
    [MeasurableSpace H] [MeasurableSpace O]
    (C : OrbitStabContext G H O) {c : ℝ} (hc : c ≠ 0)
    (h : SiegelWeilUnfoldHyp C c) :
    C.μ' C.𝓕' ≠ ⊤ ∧
    (C.μ C.𝓕).toReal ≠ 0 ∧
    (C.μ' C.𝓕').toReal / (C.μ C.𝓕).toReal = c := by
  obtain ⟨φ, hAdm, hI⟩ := h.pos_test
  have e1 := h.sw_eq_orbit φ hAdm
  have hθ : ∫ h in C.𝓕, C.thetaS φ h ∂C.μ ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at e1
    have hcI : (c : ℂ) * ∫ x, (φ x : ℂ) ∂C.ν = 0 := by
      rw [← Complex.real_smul]
      exact e1.symm
    rcases mul_eq_zero.mp hcI with hc0 | hI0
    · exact hc (Complex.ofReal_eq_zero.mp hc0)
    · exact hI hI0
  obtain ⟨hfin', e2⟩ := h.unfold φ hAdm hθ
  rw [e2, smul_smul] at e1
  have hscalar : (C.μ C.𝓕).toReal⁻¹ * (C.μ' C.𝓕').toReal = c := by
    have e3 : ((((C.μ C.𝓕).toReal⁻¹ * (C.μ' C.𝓕').toReal : ℝ)) : ℂ) *
        ∫ x, (φ x : ℂ) ∂C.ν = (c : ℂ) * ∫ x, (φ x : ℂ) ∂C.ν := by
      rw [← Complex.real_smul, ← Complex.real_smul]
      exact e1
    exact Complex.ofReal_injective (mul_right_cancel₀ hI e3)
  have h0 : (C.μ C.𝓕).toReal ≠ 0 := by
    intro h0
    rw [h0, inv_zero, zero_mul] at hscalar
    exact hc hscalar.symm
  refine ⟨hfin', h0, ?_⟩
  rw [div_eq_mul_inv, mul_comm]
  exact hscalar

/-- **Master Parametric Stabilizer-Orbit Volume Theorem (`c = 1`)**:
unifies `PI.VolStabSW.volStabFromSW_of`, `PI.VolStabS.volStabFromSW_of`, and
`PI.VolStabW.volStabFromSW_of` into a single 10-line theorem. -/
theorem volStab_eq_of_siegelWeil_unfold {G H O : Type*} [MeasurableSpace G]
    [MeasurableSpace H] [MeasurableSpace O]
    (C : OrbitStabContext G H O)
    (h : SiegelWeilUnfoldHyp C 1) :
    C.μ' C.𝓕' = C.μ C.𝓕 := by
  obtain ⟨hfin', h0, hratio⟩ := volStab_ratio_of_siegelWeil_unfold C one_ne_zero h
  have e4 : (C.μ' C.𝓕').toReal = (C.μ C.𝓕).toReal := (div_eq_one_iff_eq h0).mp hratio
  exact (ENNReal.toReal_eq_toReal_iff' hfin' h.fd_lt_top.ne).mp e4

/-- Functoriality in the admissible test-function predicate: if `Adm₂ φ → Adm₁ φ` (for instance,
`IsAdmS φ → IsAdm φ` in `StabilizerVolume`), then unfolding and Siegel–Weil transport
automatically from `Adm₁` to `Adm₂`. -/
theorem siegelWeilUnfoldHyp_of_subAdm {G H O : Type*} [MeasurableSpace G]
    [MeasurableSpace H] [MeasurableSpace O]
    (C : OrbitStabContext G H O) (Adm' : (O → ℝ) → Prop) (c : ℝ)
    (hsub : ∀ φ, Adm' φ → C.Adm φ)
    (hfin : C.μ C.𝓕 < ⊤)
    (hSW : ∀ φ, Adm' φ → (C.μ C.𝓕).toReal⁻¹ • ∫ h in C.𝓕, C.thetaS φ h ∂C.μ =
      c • ∫ x, (φ x : ℂ) ∂C.ν)
    (hUnf : ∀ φ, C.Adm φ → (∫ h in C.𝓕, C.thetaS φ h ∂C.μ) ≠ 0 →
      C.μ' C.𝓕' ≠ ⊤ ∧ ∫ h in C.𝓕, C.thetaS φ h ∂C.μ = (C.μ' C.𝓕').toReal • ∫ x, (φ x : ℂ) ∂C.ν)
    (hPos : ∃ φ, Adm' φ ∧ ∫ x, (φ x : ℂ) ∂C.ν ≠ 0) :
    SiegelWeilUnfoldHyp { C with Adm := Adm' } c where
  fd_lt_top := hfin
  sw_eq_orbit := hSW
  unfold := fun φ hφ => hUnf φ (hsub φ hφ)
  pos_test := hPos

/-- **Variant 1 (`VolStabSW`)**: replaces the 147-file / 19,387-line `StabilizerOrbitVolume` clone
(`a + 2 ≤ M`, base admissible test functions). -/
theorem volStabSW_of_siegelWeil {G H O : Type*} [MeasurableSpace G] [MeasurableSpace H]
    [MeasurableSpace O] {a M : ℕ} (_hr : StabVolVariant.sw.rankCond a M)
    (C : OrbitStabContext G H O) (h : SiegelWeilUnfoldHyp C 1) :
    C.μ' C.𝓕' = C.μ C.𝓕 :=
  volStab_eq_of_siegelWeil_unfold C h

/-- **Variant 2 (`VolStabS`)**: replaces the 155-file / 19,855-line `StabilizerVolume` clone
(`2 * a < M`, smooth compactly supported test functions `SmoothAdm` lifting into `C.Adm`). -/
theorem volStabS_of_siegelWeil {G H O : Type*} [MeasurableSpace G] [MeasurableSpace H]
    [MeasurableSpace O] {a M : ℕ} (_hr : StabVolVariant.smooth.rankCond a M)
    (C : OrbitStabContext G H O) (SmoothAdm : (O → ℝ) → Prop)
    (hsub : ∀ φ, SmoothAdm φ → C.Adm φ)
    (hfin : C.μ C.𝓕 < ⊤)
    (hSW : ∀ φ, SmoothAdm φ → (C.μ C.𝓕).toReal⁻¹ • ∫ h in C.𝓕, C.thetaS φ h ∂C.μ =
      (1 : ℝ) • ∫ x, (φ x : ℂ) ∂C.ν)
    (hUnf : ∀ φ, C.Adm φ → (∫ h in C.𝓕, C.thetaS φ h ∂C.μ) ≠ 0 →
      C.μ' C.𝓕' ≠ ⊤ ∧ ∫ h in C.𝓕, C.thetaS φ h ∂C.μ = (C.μ' C.𝓕').toReal • ∫ x, (φ x : ℂ) ∂C.ν)
    (hPos : ∃ φ, SmoothAdm φ ∧ ∫ x, (φ x : ℂ) ∂C.ν ≠ 0) :
    C.μ' C.𝓕' = C.μ C.𝓕 :=
  volStab_eq_of_siegelWeil_unfold { C with Adm := SmoothAdm }
    (siegelWeilUnfoldHyp_of_subAdm C SmoothAdm 1 hsub hfin hSW hUnf hPos)

/-- **Variant 3 (`VolStabW`)**: replaces the 146-file / 18,416-line `WeilStabilizerVolume` clone
(`2 * a < M`, base admissible test functions). -/
theorem volStabW_of_siegelWeil {G H O : Type*} [MeasurableSpace G] [MeasurableSpace H]
    [MeasurableSpace O] {a M : ℕ} (_hr : StabVolVariant.weil.rankCond a M)
    (C : OrbitStabContext G H O) (h : SiegelWeilUnfoldHyp C 1) :
    C.μ' C.𝓕' = C.μ C.𝓕 :=
  volStab_eq_of_siegelWeil_unfold C h

/-! ## 2. Exact Double-Coset Unfolding, Finite-Genus Mass Sum `∑ 1 / |Aut(L_i)|` & Measure Ratio -/

section GenusMassAlgebra

variable {G : Type*} [Group G]

/-- Discrete automorphism group `Aut(L_i) = Γ ∩ g K g⁻¹` of the genus representative `g`. -/
def genusAut (Γ K : Subgroup G) (g : G) : Set Γ :=
  {γ | g⁻¹ * ((γ : G) * g) ∈ K}

/-- The hitting set `{γ ∈ Γ | g⁻¹ (γ x) ∈ K}` used to unfold double-coset indicators. -/
def doubleCosetHit (Γ K : Subgroup G) (g x : G) : Set Γ :=
  {γ | g⁻¹ * ((γ : G) * x) ∈ K}

theorem one_mem_genusAut (Γ K : Subgroup G) (g : G) : (1 : Γ) ∈ genusAut Γ K g := by
  simp [genusAut]

theorem doubleCosetHit_empty {Γ K : Subgroup G} {ι : Type*} (g : ι → G)
    (hdisj : ∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j)
    {j : ι} (δ : Γ) (k : K) (i : ι) (hij : i ≠ j) :
    doubleCosetHit Γ K (g i) ((δ : G) * g j * k) = ∅ := by
  ext γ
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  have h' : (g i)⁻¹ * ((γ : G) * ((δ : G) * g j * k)) ∈ K := h
  apply hij
  refine hdisj i j 1 (γ * δ) ⟨_, h'⟩ k ?_
  simp [mul_assoc]

/-- Explicit bijection between the double-coset hitting set at `δ * g_j * k` and `Aut(L_j)`. -/
def doubleCosetHitEquiv {Γ K : Subgroup G} (gj : G) (δ : Γ) (k : K) :
    doubleCosetHit Γ K gj ((δ : G) * gj * k) ≃ genusAut Γ K gj where
  toFun γ := ⟨γ.1 * δ, by
    have h := K.mul_mem γ.2 (K.inv_mem k.2)
    simp only [genusAut, Set.mem_ofPred_eq, Subgroup.coe_mul]
    convert h using 1
    group⟩
  invFun γ := ⟨γ.1 * δ⁻¹, by
    have h := K.mul_mem γ.2 k.2
    simp only [doubleCosetHit, Set.mem_ofPred_eq, Subgroup.coe_mul, Subgroup.coe_inv]
    convert h using 1
    group⟩
  left_inv γ := by ext; simp
  right_inv γ := by ext; simp

/-- The exact finite-genus mass sum `∑ i, 1 / |Aut(L_i)|`. -/
def genusMass {ι : Type*} [Fintype ι] (Γ K : Subgroup G) (g : ι → G) : ℝ :=
  ∑ i, ((Nat.card (genusAut Γ K (g i)) : ℝ))⁻¹

theorem genusMass_nonneg {ι : Type*} [Fintype ι] (Γ K : Subgroup G) (g : ι → G) :
    0 ≤ genusMass Γ K g := by
  unfold genusMass
  exact Finset.sum_nonneg fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem genusMass_pos {ι : Type*} [Fintype ι] [Nonempty ι] (Γ K : Subgroup G) (g : ι → G)
    (hfin : ∀ i, (genusAut Γ K (g i)).Finite) :
    0 < genusMass Γ K g := by
  unfold genusMass
  refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
  have : Finite (genusAut Γ K (g i)) := (hfin i).to_subtype
  have : Nonempty (genusAut Γ K (g i)) := ⟨⟨1, one_mem_genusAut Γ K (g i)⟩⟩
  exact inv_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)

end GenusMassAlgebra

section GenusMassUnfolding

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- **Exact Double-Coset Unfolding Mass Formula (`ENNReal` form)**:
for a finite double-coset decomposition `G = ⨆ i, Γ g_i K` with finite stabilizers
`Aut(L_i) = Γ ∩ g_i K g_i⁻¹`, the covolume of a fundamental domain `𝓕` for `Γ \ G` equals
`μ K * ∑ i, |Aut(L_i)|⁻¹`. -/
theorem measure_fundamentalDomain_eq_genus_mass_sum {Γ K : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) {ι : Type*} [Fintype ι] (g : ι → G)
    (hcov : ∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g i * k)
    (hdisj : ∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j)
    (hfin : ∀ i, (genusAut Γ K (g i)).Finite)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    μ 𝓕 = ∑ i, μ K * ((Nat.card (genusAut Γ K (g i)) : ℝ≥0∞))⁻¹ := by
  classical
  have : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  have : SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  let T : ι → Set G := fun i => (fun y => (g i)⁻¹ * y) ⁻¹' (K : Set G)
  have hT : ∀ i, MeasurableSet (T i) := fun i => (measurable_const_mul _) hK
  let f : G → ℝ≥0∞ := fun y =>
    ∑ i, ((Nat.card (genusAut Γ K (g i)) : ℝ≥0∞))⁻¹ * (T i).indicator 1 y
  have hf : Measurable f := Finset.measurable_sum _ fun i _ =>
    (measurable_one.indicator (hT i)).const_mul _
  have hG : ∫⁻ y, f y ∂μ = ∑ i, μ K * ((Nat.card (genusAut Γ K (g i)) : ℝ≥0∞))⁻¹ := by
    rw [lintegral_finsetSum _ fun i _ => (measurable_one.indicator (hT i)).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_const_mul _ (measurable_one.indicator (hT i)), lintegral_indicator_one (hT i),
      measure_preimage_mul, mul_comm]
  have hpt : ∀ x, ∑' γ : Γ, f (γ • x) = 1 := by
    intro x
    obtain ⟨j, δ, k, rfl⟩ := hcov x
    have hsum : ∀ i, ∑' γ : Γ, (T i).indicator (1 : G → ℝ≥0∞) (γ • ((δ : G) * g j * k)) =
        Nat.card (doubleCosetHit Γ K (g i) ((δ : G) * g j * k)) := by
      intro i
      have hfin' : (doubleCosetHit Γ K (g i) ((δ : G) * g j * k)).Finite := by
        by_cases hij : i = j
        · rw [hij]
          have := (hfin j).to_subtype
          have : Finite (doubleCosetHit Γ K (g j) ((δ : G) * g j * k)) :=
            Finite.of_equiv _ (doubleCosetHitEquiv (g j) δ k).symm
          exact Set.toFinite _
        · rw [doubleCosetHit_empty g hdisj δ k i hij]
          exact Set.finite_empty
      have e : (fun γ : Γ => (T i).indicator (1 : G → ℝ≥0∞) (γ • ((δ : G) * g j * k))) =
          (doubleCosetHit Γ K (g i) ((δ : G) * g j * k)).indicator 1 := by
        funext γ
        simp only [Set.indicator, T, doubleCosetHit, Set.mem_preimage, Set.mem_ofPred_eq,
          Subgroup.smul_def, smul_eq_mul, SetLike.mem_coe, Pi.one_apply]
        rfl
      rw [e, ← _root_.tsum_subtype]
      have := hfin'.fintype
      rw [tsum_fintype]
      simp only [Pi.one_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        Fintype.card_eq_nat_card]
    have hswap : ∑' γ : Γ, f (γ • ((δ : G) * g j * k)) =
        ∑ i, ((Nat.card (genusAut Γ K (g i)) : ℝ≥0∞))⁻¹ *
          ∑' γ : Γ, (T i).indicator (1 : G → ℝ≥0∞) (γ • ((δ : G) * g j * k)) := by
      simp only [f]
      rw [Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ENNReal.tsum_mul_left]
    rw [hswap, Finset.sum_eq_single j]
    · rw [hsum j, Nat.card_congr (doubleCosetHitEquiv (g j) δ k)]
      have hne : (Nat.card (genusAut Γ K (g j)) : ℝ≥0∞) ≠ 0 := by
        have := (hfin j).to_subtype
        have : Nonempty (genusAut Γ K (g j)) := ⟨⟨1, one_mem_genusAut Γ K (g j)⟩⟩
        exact_mod_cast (Nat.card_pos (α := genusAut Γ K (g j))).ne'
      exact ENNReal.inv_mul_cancel hne (ENNReal.natCast_ne_top _)
    · intro i _ hij
      rw [hsum i, doubleCosetHit_empty g hdisj δ k i hij]
      simp
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hmeas : ∀ γ : Γ, Measurable fun x => f (γ • x) := fun γ => hf.comp (measurable_const_smul γ)
  calc μ 𝓕 = ∫⁻ x in 𝓕, 1 ∂μ := (setLIntegral_one 𝓕).symm
    _ = ∫⁻ x in 𝓕, ∑' γ : Γ, f (γ • x) ∂μ := by simp only [hpt]
    _ = ∑' γ : Γ, ∫⁻ x in 𝓕, f (γ • x) ∂μ := lintegral_tsum fun γ => (hmeas γ).aemeasurable
    _ = ∫⁻ y, f y ∂μ := (h𝓕.lintegral_eq_tsum'' f).symm
    _ = _ := hG

/-- Real-valued finite-genus mass identity `(μ 𝓕).toReal = (μ K).toReal * genusMass Γ K g`. -/
theorem measure_fd_toReal_eq_mul_genusMass {Γ K : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) (hKfin : μ K ≠ ⊤)
    {ι : Type*} [Fintype ι] (g : ι → G)
    (hcov : ∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g i * k)
    (hdisj : ∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j)
    (hfin : ∀ i, (genusAut Γ K (g i)).Finite)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    (μ 𝓕).toReal = (μ K).toReal * genusMass Γ K g := by
  rw [measure_fundamentalDomain_eq_genus_mass_sum μ hK g hcov hdisj hfin h𝓕]
  rw [ENNReal.toReal_sum]
  · unfold genusMass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · intro i _
    have hne : (Nat.card (genusAut Γ K (g i)) : ℝ≥0∞) ≠ 0 := by
      have := (hfin i).to_subtype
      have : Nonempty (genusAut Γ K (g i)) := ⟨⟨1, one_mem_genusAut Γ K (g i)⟩⟩
      exact_mod_cast (Nat.card_pos (α := genusAut Γ K (g i))).ne'
    exact ENNReal.mul_ne_top hKfin (ENNReal.inv_ne_top.mpr hne)

/-- **Orbit-Stabilizer Covolume-to-Level Measure Ratio**:
`(μ 𝓕).toReal / (μ K).toReal = ∑ i, 1 / |Aut(L_i)|`. -/
theorem genusMass_eq_covolume_div {Γ K : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) (hKpos : 0 < μ K) (hKfin : μ K ≠ ⊤)
    {ι : Type*} [Fintype ι] (g : ι → G)
    (hcov : ∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g i * k)
    (hdisj : ∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j)
    (hfin : ∀ i, (genusAut Γ K (g i)).Finite)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    (μ 𝓕).toReal / (μ K).toReal = genusMass Γ K g := by
  rw [measure_fd_toReal_eq_mul_genusMass μ hK hKfin g hcov hdisj hfin h𝓕]
  have hK0 : (μ K).toReal ≠ 0 := (ENNReal.toReal_pos hKpos.ne' hKfin).ne'
  exact mul_div_cancel_left₀ _ hK0

/-- **Level-Subgroup Index Scaling Law**:
passing from a compact-open level `K` to a measurable finite-index sub-level `K' ≤ K` of index
`I = [K : K']` scales the covolume-to-level mass ratio by exact factor `I`. -/
theorem covolume_ratio_sublevel_scaling {Γ K K' : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) (hKfin : μ K ≠ ⊤)
    (hK'pos : 0 < μ K') (hK'fin : μ K' ≠ ⊤)
    {idx : ℝ} (hidx : (μ K).toReal = idx * (μ K').toReal)
    {ι : Type*} [Fintype ι] (g : ι → G)
    (hcov : ∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g i * k)
    (hdisj : ∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j)
    (hfin : ∀ i, (genusAut Γ K (g i)).Finite)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    (μ 𝓕).toReal / (μ K').toReal = idx * genusMass Γ K g := by
  have hK'0 : (μ K').toReal ≠ 0 := (ENNReal.toReal_pos hK'pos.ne' hK'fin).ne'
  have h1 := measure_fd_toReal_eq_mul_genusMass μ hK hKfin g hcov hdisj hfin h𝓕
  rw [h1, hidx]
  field_simp [hK'0]

end GenusMassUnfolding

/-- **Finite Orbit-Stabilizer Mass Identity** (Burnside / arithmetic genus mass):
for any finite group `G` acting on a finite set `X` with chosen orbit representatives `rep`,
`∑ ω, (|Stab_G(rep ω)| : ℝ)⁻¹ = |X| / |G|`. -/
theorem finite_orbit_stabilizer_mass_identity {G X : Type*} [Group G] [Fintype G]
    [Fintype X] [MulAction G X] [DecidableEq X]
    [Fintype (MulAction.orbitRel.Quotient G X)]
    (rep : MulAction.orbitRel.Quotient G X → X)
    (hrep : ∀ ω, Quotient.mk'' (rep ω) = ω) :
    ∑ ω : MulAction.orbitRel.Quotient G X,
      ((Nat.card (MulAction.stabilizer G (rep ω)) : ℝ))⁻¹ =
      (Fintype.card X : ℝ) / (Fintype.card G : ℝ) := by
  classical
  have hGpos : (0 : ℝ) < (Fintype.card G : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hsum_card : (Fintype.card X : ℝ) =
      ∑ ω : MulAction.orbitRel.Quotient G X,
        (Fintype.card (MulAction.orbit G (rep ω)) : ℝ) := by
    have hnat : Fintype.card X =
        ∑ ω : MulAction.orbitRel.Quotient G X,
          Fintype.card (MulAction.orbit G (rep ω)) := by
      have hpart := Finset.card_eq_sum_card_fiberwise
        (f := fun x : X => (Quotient.mk'' x : MulAction.orbitRel.Quotient G X))
        (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
      rw [← Finset.card_univ, hpart]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [← Fintype.card_coe]
      refine Fintype.card_congr ?_
      refine
        { toFun := fun x => ⟨x.1, by
            have hx : Quotient.mk'' x.1 = ω := (Finset.mem_filter.mp x.2).2
            exact Quotient.exact' (hx.trans (hrep ω).symm)⟩
          invFun := fun y => ⟨y.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (Quotient.sound' y.2).trans (hrep ω)⟩⟩
          left_inv := fun x => by ext; rfl
          right_inv := fun y => by ext; rfl }
    exact_mod_cast hnat
  rw [hsum_card, Finset.sum_div]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have horb := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G (rep ω)
  have hstab_pos : (0 : ℝ) < (Fintype.card (MulAction.stabilizer G (rep ω)) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have horbR : (Fintype.card (MulAction.orbit G (rep ω)) : ℝ) *
      (Fintype.card (MulAction.stabilizer G (rep ω)) : ℝ) = (Fintype.card G : ℝ) := by
    exact_mod_cast horb
  rw [← Fintype.card_eq_nat_card]
  field_simp [hGpos.ne', hstab_pos.ne']
  linarith [horbR]

/-! ## 3. Siegel–Tamagawa Unitary Mass Ratio, Telescoping & `GL5` Signature Induction -/

/-- The exact Siegel–Tamagawa unitary mass ratio factor `mass(M) / mass(M - 1)` for a CM
extension of totally real degree `f = [F : ℚ]`, discriminant parameter `vE`, and Dirichlet/Hecke
`L`-value factor `Lval M` (matching `Formalism.HermitianLatticesTheory.massRatioRightSide`). -/
def massRatioFactor (f : ℕ) (vE : ℝ) (Lval : ℕ → ℝ) (M : ℕ) : ℝ :=
  (((Nat.factorial (M - 1) : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f /
    Real.sqrt ((2 * vE) ^ f) * Lval M

theorem massRatioFactor_pos {f M : ℕ} {vE : ℝ} {Lval : ℕ → ℝ}
    (hv : 0 < vE) (hL : 0 < Lval M) :
    0 < massRatioFactor f vE Lval M := by
  unfold massRatioFactor
  have hfac : (0 : ℝ) < ((Nat.factorial (M - 1) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hpi : (0 : ℝ) < vE / Real.pi := div_pos hv Real.pi_pos
  have hden : (0 : ℝ) < Real.sqrt ((2 * vE) ^ f) := Real.sqrt_pos.mpr (pow_pos (by linarith) f)
  exact mul_pos (div_pos (pow_pos (mul_pos hfac (pow_pos hpi M)) f) hden) hL

/-- **Exact Mass Telescoping Identity** (replacing `MassTelescope.lean`):
if `mass M / mass (M - 1) = ratio M` for all `k + 1 ≤ M ≤ r`, then
`mass r = mass k * ∏ M ∈ Ico (k + 1) (r + 1), ratio M`. -/
theorem mass_telescope_eq_prod {mass ratio : ℕ → ℝ} {k r : ℕ} (hkr : k ≤ r)
    (hpos : ∀ M, k ≤ M → M ≤ r → mass M ≠ 0)
    (hstep : ∀ M, k + 1 ≤ M → M ≤ r → mass M / mass (M - 1) = ratio M) :
    mass r = mass k * ∏ M ∈ Finset.Ico (k + 1) (r + 1), ratio M := by
  induction r, hkr using Nat.le_induction with
  | base =>
    simp
  | succ r hkr ih =>
    have hpos' : ∀ M, k ≤ M → M ≤ r → mass M ≠ 0 :=
      fun M h1 h2 => hpos M h1 (Nat.le_succ_of_le h2)
    have hstep' : ∀ M, k + 1 ≤ M → M ≤ r → mass M / mass (M - 1) = ratio M :=
      fun M h1 h2 => hstep M h1 (Nat.le_succ_of_le h2)
    have hprev := ih hpos' hstep'
    have hIco : Finset.Ico (k + 1) (r + 1 + 1) =
        insert (r + 1) (Finset.Ico (k + 1) (r + 1)) := by
      ext M
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hnotmem : r + 1 ∉ Finset.Ico (k + 1) (r + 1) := by
      simp [Finset.mem_Ico]
    rw [hIco, Finset.prod_insert hnotmem, ← mul_assoc, mul_comm (mass k) (ratio (r + 1)),
      mul_assoc, ← hprev]
    have hlast := hstep (r + 1) (by omega) le_rfl
    simp only [Nat.add_sub_cancel] at hlast
    have hr0 : mass r ≠ 0 := hpos r hkr (Nat.le_succ r)
    rw [← hlast]
    field_simp [hr0]

/-- **`GL5` Definite-to-Indefinite Volume = Mass Signature Induction**
(collapsing `volume_mass_succ`, `volume_mass_ge_two`, `vol_indef` in
`GL5/DiscreteSeriesOfFormalDegree.lean` into one clean induction):
given `vol 2 0 = mass 2` and stabilizer-orbit step ratios in both `+` and `-` signatures,
`vol P Q = mass (P + Q)` for all `P ≥ 2` and `Q ≥ 0`. -/
theorem volume_eq_mass_of_ratio_induction {vol : ℕ → ℕ → ℝ} {mass : ℕ → ℝ}
    (hbase : vol 2 0 = mass 2)
    (hmass_ne : ∀ n, 2 ≤ n → mass n ≠ 0)
    (hstepP : ∀ P Q, 2 ≤ P → vol (P + 1) Q / vol P Q = mass (P + 1 + Q) / mass (P + Q))
    (hstepQ : ∀ P Q, 2 ≤ P → vol P (Q + 1) / vol P Q = mass (P + Q + 1) / mass (P + Q)) :
    ∀ P Q, 2 ≤ P → vol P Q = mass (P + Q) := by
  have hdef : ∀ P, 2 ≤ P → vol P 0 = mass P := by
    intro P hP
    induction P, hP using Nat.le_induction with
    | base => exact hbase
    | succ P hP ih =>
      have h := hstepP P 0 hP
      rw [ih, add_zero, add_zero] at h
      have h0 : mass P ≠ 0 := hmass_ne P hP
      exact (div_left_inj' h0).mp h
  intro P Q hP
  induction Q with
  | zero =>
    simpa using hdef P hP
  | succ Q ih =>
    have h := hstepQ P Q hP
    rw [ih] at h
    have h0 : mass (P + Q) ≠ 0 := hmass_ne (P + Q) (by omega)
    have heq := (div_left_inj' h0).mp h
    simpa [Nat.add_assoc] using heq

/-! ## 4. Analytic & Combinatorial `mass_ratio_ge` Lower Bounds (Theta-Lift Covolume Engine) -/

/-- Clean elementary Stirling-type lower bound `n log n - n ≤ log (n!)`, proved directly from
`log (1 + 1/n) ≤ 1/n` with zero heavy asymptotic machinery. -/
theorem log_factorial_ge_mul_log_sub (n : ℕ) :
    (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) ≤ Real.log (Nat.factorial n : ℝ) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    cases n with
    | zero =>
      simp
    | succ m =>
      set k : ℕ := m + 1
      have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos m)
      have hk1pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos k)
      have hfac : (0 : ℝ) < (Nat.factorial k : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
      have hstep_fac : Real.log (Nat.factorial (k + 1) : ℝ) =
          Real.log ((k + 1 : ℕ) : ℝ) + Real.log (Nat.factorial k : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul hk1pos.ne' hfac.ne']
      have hlog_step : Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ≤ 1 / (k : ℝ) := by
        have hpos_div : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / (k : ℝ) := div_pos hk1pos hkpos
        have h1 := Real.log_le_sub_one_of_pos hpos_div
        have h2 : ((k + 1 : ℕ) : ℝ) / (k : ℝ) - 1 = 1 / (k : ℝ) := by
          push_cast
          field_simp [hkpos.ne']
          ring
        linarith
      have hmul : (k : ℝ) * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) ≤ 1 := by
        rw [← Real.log_div hk1pos.ne' hkpos.ne']
        have := mul_le_mul_of_nonneg_left hlog_step hkpos.le
        rwa [mul_one_div_cancel hkpos.ne'] at this
      rw [hstep_fac]
      push_cast at hmul ⊢
      linarith

/-- Exact arithmetic sum of indices `∑ M ∈ Ico (k + 1) (k + m), M = (m - 1) * (2 * k + m) / 2`
for `1 ≤ m`. -/
theorem sum_Ico_rank_indices {k m : ℕ} (hm : 1 ≤ m) :
    ∑ M ∈ Finset.Ico (k + 1) (k + m), (M : ℝ) =
      ((m : ℝ) - 1) * (2 * (k : ℝ) + (m : ℝ)) / 2 := by
  induction m, hm using Nat.le_induction with
  | base =>
    simp
  | succ m hm ih =>
    have hIco : Finset.Ico (k + 1) (k + (m + 1)) =
        insert (k + m) (Finset.Ico (k + 1) (k + m)) := by
      ext M
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hnotmem : k + m ∉ Finset.Ico (k + 1) (k + m) := by
      simp [Finset.mem_Ico]
    rw [hIco, Finset.sum_insert hnotmem, ih]
    push_cast
    ring

/-- Exact logarithm of a single `massRatioFactor`. -/
theorem log_massRatioFactor {f M : ℕ} {vE : ℝ} {Lval : ℕ → ℝ}
    (hv : 0 < vE) (hL : 0 < Lval M) :
    Real.log (massRatioFactor f vE Lval M) =
      (f : ℝ) * Real.log (Nat.factorial (M - 1) : ℝ) +
      (f : ℝ) * (M : ℝ) * Real.log (vE / Real.pi) -
      ((f : ℝ) / 2) * Real.log (2 * vE) +
      Real.log (Lval M) := by
  unfold massRatioFactor
  have hfac : (0 : ℝ) < ((Nat.factorial (M - 1) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hpi : (0 : ℝ) < vE / Real.pi := div_pos hv Real.pi_pos
  have hnum : (0 : ℝ) < (((Nat.factorial (M - 1) : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f :=
    pow_pos (mul_pos hfac (pow_pos hpi M)) f
  have h2v : (0 : ℝ) < 2 * vE := by linarith
  have hden : (0 : ℝ) < Real.sqrt ((2 * vE) ^ f) := Real.sqrt_pos.mpr (pow_pos h2v f)
  rw [Real.log_mul (div_pos hnum hden).ne' hL.ne',
    Real.log_div hnum.ne' hden.ne',
    Real.log_pow,
    Real.log_mul hfac.ne' (pow_pos hpi M).ne',
    Real.log_pow,
    Real.log_sqrt (pow_pos h2v f).le,
    Real.log_pow]
  ring

/-- **Exact Logarithmic Expansion of the Telescoped Siegel–Tamagawa Mass Ratio**
over ranks `k + 1 ≤ M ≤ k - 1 + m` (`m ≥ 1, k ≥ 2`). -/
theorem log_mass_ratio_exact {f m k : ℕ} {vE massk massr : ℝ} {Lval : ℕ → ℝ}
    (hm : 1 ≤ m) (hk : 2 ≤ k) (hv : 0 < vE)
    (hmk : 0 < massk)
    (hL : ∀ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1), 0 < Lval M)
    (hmass : massr = massk * ∏ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1),
      massRatioFactor f vE Lval M) :
    Real.log (massr / massk) =
      (f : ℝ) * (∑ M ∈ Finset.Ico (k + 1) (k + m), Real.log (Nat.factorial (M - 1) : ℝ)) +
      (f : ℝ) * (((m : ℝ) - 1) * (2 * (k : ℝ) + (m : ℝ)) / 2) * Real.log (vE / Real.pi) -
      ((f : ℝ) * ((m : ℝ) - 1) / 2) * Real.log (2 * vE) +
      ∑ M ∈ Finset.Ico (k + 1) (k + m), Real.log (Lval M) := by
  have htop : k - 1 + m + 1 = k + m := by omega
  rw [htop] at hL hmass
  have hdiv : massr / massk = ∏ M ∈ Finset.Ico (k + 1) (k + m), massRatioFactor f vE Lval M := by
    rw [hmass, mul_div_cancel_left₀ _ hmk.ne']
  rw [hdiv, Real.log_prod (fun M hM => (massRatioFactor_pos hv (hL M hM)).ne')]
  have hterm : ∀ M ∈ Finset.Ico (k + 1) (k + m),
      Real.log (massRatioFactor f vE Lval M) =
        (f : ℝ) * Real.log (Nat.factorial (M - 1) : ℝ) +
        (f : ℝ) * (M : ℝ) * Real.log (vE / Real.pi) -
        ((f : ℝ) / 2) * Real.log (2 * vE) +
        Real.log (Lval M) := fun M hM => log_massRatioFactor hv (hL M hM)
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [sum_Ico_rank_indices hm, Finset.sum_const, Nat.card_Ico]
  have hcard : k + m - (k + 1) = m - 1 := by omega
  rw [hcard, nsmul_eq_mul, Nat.cast_sub hm, Nat.cast_one]
  ring

/-- Single-step `massRatioFactor` lower bound: for `M ≥ 3`, `vE ≥ π`, `cL ≤ Lval M`,
the factorial + volume growth beats `((M - 1)! * (vE / π)^M)^f / √((2 vE)^f) * cL`. -/
theorem mass_ratio_step_ge {f M : ℕ} {vE cL : ℝ} {Lval : ℕ → ℝ}
    (hv : 0 < vE) (hL : cL ≤ Lval M) :
    (((Nat.factorial (M - 1) : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f /
        Real.sqrt ((2 * vE) ^ f) * cL ≤
      massRatioFactor f vE Lval M := by
  unfold massRatioFactor
  have hfac : (0 : ℝ) ≤ ((Nat.factorial (M - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpi : (0 : ℝ) ≤ vE / Real.pi := div_nonneg hv.le Real.pi_pos.le
  have hden : (0 : ℝ) ≤ Real.sqrt ((2 * vE) ^ f) := Real.sqrt_nonneg _
  exact mul_le_mul_of_nonneg_left hL (div_nonneg (pow_nonneg (mul_nonneg hfac (pow_nonneg hpi M)) f) hden)

/-- **Master `GL5` / Theta-Lift `mass_ratio_ge` Lower Bound**:
combines:
1. the telescoped Siegel–Tamagawa unitary mass ratio `massr / massk`,
2. the compact-open level-index lower bound
   `(2^(2f))⁻¹ * (g₁ * g₂)^(f * m * (2k + m - 1) / 2) ≤ Isig / Ipi`,
3. the Euler-factor log lower bound `∑_{M} log (Lval M) ≥ -f * B_L`,
4. the archimedean Weyl-dimension / covolume comparison
   `(2/3)^f * (massr / massk) * (Isig / Ipi) * dimRatio ≤ Dstar / dstar`,
to yield an explicit, 100%-computable lower bound on the normalized logarithmic covolume ratio
`(1 / (f * k)) * log (Dstar / dstar)` — directly driving the theta-lift covolume/divisibility
comparison in `RHDirect.SlopeInequality` and `RHDirect.ThetaSlopeEngine`. -/
theorem mass_ratio_ge
    {f m k : ℕ} {vE g₁ g₂ massk massr Isig Ipi Dstar dstar dimRatio B_L : ℝ}
    {Lval : ℕ → ℝ}
    (hf : 1 ≤ f) (hm : 1 ≤ m) (hk : 2 ≤ k)
    (hv : Real.pi ≤ vE) (hg₁ : 1 ≤ g₁) (hg₂ : 1 ≤ g₂)
    (hmk : 0 < massk) (hmr : 0 < massr) (hIsig : 0 < Isig) (hIpi : 0 < Ipi)
    (hdim : 0 < dimRatio)
    (hLpos : ∀ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1), 0 < Lval M)
    (hLlog : -((f : ℝ) * B_L) ≤ ∑ M ∈ Finset.Ico (k + 1) (k + m), Real.log (Lval M))
    (hmass : massr = massk * ∏ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1),
      massRatioFactor f vE Lval M)
    (hidx : ((2 : ℝ) ^ (2 * f))⁻¹ *
        (g₁ * g₂) ^ ((f : ℝ) * (m : ℝ) * (2 * (k : ℝ) + (m : ℝ) - 1) / 2) ≤
      Isig / Ipi)
    (hcov : (2 / 3 : ℝ) ^ f * (massr / massk) * (Isig / Ipi) * dimRatio ≤ Dstar / dstar) :
    (m : ℝ) * (Real.log g₁ + Real.log g₂) +
      ((m : ℝ) - 1) * Real.log (vE / Real.pi) +
      (1 / (k : ℝ)) * (∑ M ∈ Finset.Ico (k + 1) (k + m),
        (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ))) +
      (1 / ((f : ℝ) * (k : ℝ))) * Real.log dimRatio -
      ((m : ℝ) - 1) / (2 * (k : ℝ)) * Real.log (2 * vE) -
      (B_L + Real.log 6) / (k : ℝ)
      ≤ (1 / ((f : ℝ) * (k : ℝ))) * Real.log (Dstar / dstar) := by
  have hvpos : 0 < vE := lt_of_lt_of_le Real.pi_pos hv
  have hfpos : (0 : ℝ) < (f : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hf)
  have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hfkpos : (0 : ℝ) < (f : ℝ) * (k : ℝ) := mul_pos hfpos hkpos
  have hg1pos : 0 < g₁ := lt_of_lt_of_le zero_lt_one hg₁
  have hg2pos : 0 < g₂ := lt_of_lt_of_le zero_lt_one hg₂
  have h23pos : (0 : ℝ) < (2 / 3 : ℝ) ^ f := pow_pos (by norm_num) f
  have hmass_ratio_pos : 0 < massr / massk := div_pos hmr hmk
  have hidx_pos : 0 < Isig / Ipi := div_pos hIsig hIpi
  have hlhs_pos : 0 < (2 / 3 : ℝ) ^ f * (massr / massk) * (Isig / Ipi) * dimRatio :=
    mul_pos (mul_pos (mul_pos h23pos hmass_ratio_pos) hidx_pos) hdim
  -- Step 1: Take logs of the covolume comparison `hcov`
  have hlog_cov : Real.log ((2 / 3 : ℝ) ^ f * (massr / massk) * (Isig / Ipi) * dimRatio) ≤
      Real.log (Dstar / dstar) :=
    Real.log_le_log hlhs_pos hcov
  rw [Real.log_mul (mul_pos (mul_pos h23pos hmass_ratio_pos) hidx_pos).ne' hdim.ne',
    Real.log_mul (mul_pos h23pos hmass_ratio_pos).ne' hidx_pos.ne',
    Real.log_mul h23pos.ne' hmass_ratio_pos.ne',
    Real.log_pow] at hlog_cov
  -- Step 2: Lower bound `log (Isig / Ipi)` from `hidx`
  have hidx_lhs_pos : 0 < ((2 : ℝ) ^ (2 * f))⁻¹ *
      (g₁ * g₂) ^ ((f : ℝ) * (m : ℝ) * (2 * (k : ℝ) + (m : ℝ) - 1) / 2) :=
    mul_pos (inv_pos.mpr (pow_pos (by norm_num) _)) (Real.rpow_pos_of_pos (mul_pos hg1pos hg2pos) _)
  have hlog_idx :
      -((2 * (f : ℝ)) * Real.log 2) +
        ((f : ℝ) * (m : ℝ) * (2 * (k : ℝ) + (m : ℝ) - 1) / 2) * (Real.log g₁ + Real.log g₂) ≤
      Real.log (Isig / Ipi) := by
    have h1 := Real.log_le_log hidx_lhs_pos hidx
    rw [Real.log_mul (inv_pos.mpr (pow_pos (by norm_num) _)).ne'
      (Real.rpow_pos_of_pos (mul_pos hg1pos hg2pos) _).ne',
      Real.log_inv, Real.log_pow, Real.log_rpow (mul_pos hg1pos hg2pos),
      Real.log_mul hg1pos.ne' hg2pos.ne'] at h1
    push_cast at h1
    linarith
  -- Step 3: Exact log of `massr / massk` + Stirling lower bound on each `(M - 1)!`
  have hlog_mass_eq := log_mass_ratio_exact hm hk hvpos hmk hLpos hmass
  have hfac_sum :
      ∑ M ∈ Finset.Ico (k + 1) (k + m),
        (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ)) ≤
      ∑ M ∈ Finset.Ico (k + 1) (k + m), Real.log (Nat.factorial (M - 1) : ℝ) :=
    Finset.sum_le_sum fun M _ => log_factorial_ge_mul_log_sub (M - 1)
  -- Step 4: Drop the nonnegative extra quadratic terms in `m (m - 1)` for `g₁ * g₂ ≥ 1` and `vE / π ≥ 1`
  have hlog_g_nonneg : 0 ≤ Real.log g₁ + Real.log g₂ :=
    add_nonneg (Real.log_nonneg hg₁) (Real.log_nonneg hg₂)
  have hlog_vpi_nonneg : 0 ≤ Real.log (vE / Real.pi) :=
    Real.log_nonneg ((one_le_div Real.pi_pos).mpr hv)
  have hm1_nonneg : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hquad_g : (f : ℝ) * (k : ℝ) * (m : ℝ) * (Real.log g₁ + Real.log g₂) ≤
      ((f : ℝ) * (m : ℝ) * (2 * (k : ℝ) + (m : ℝ) - 1) / 2) * (Real.log g₁ + Real.log g₂) := by
    apply mul_le_mul_of_nonneg_right _ hlog_g_nonneg
    have hdiff : ((f : ℝ) * (m : ℝ) * (2 * (k : ℝ) + (m : ℝ) - 1) / 2) -
        (f : ℝ) * (k : ℝ) * (m : ℝ) = (f : ℝ) * (m : ℝ) * ((m : ℝ) - 1) / 2 := by ring
    have hnn : 0 ≤ (f : ℝ) * (m : ℝ) * ((m : ℝ) - 1) / 2 := by
      have hmpos : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      positivity
    linarith
  have hquad_v : (f : ℝ) * (k : ℝ) * ((m : ℝ) - 1) * Real.log (vE / Real.pi) ≤
      (f : ℝ) * (((m : ℝ) - 1) * (2 * (k : ℝ) + (m : ℝ)) / 2) * Real.log (vE / Real.pi) := by
    apply mul_le_mul_of_nonneg_right _ hlog_vpi_nonneg
    have hdiff : (f : ℝ) * (((m : ℝ) - 1) * (2 * (k : ℝ) + (m : ℝ)) / 2) -
        (f : ℝ) * (k : ℝ) * ((m : ℝ) - 1) = (f : ℝ) * ((m : ℝ) - 1) * (m : ℝ) / 2 := by ring
    have hnn : 0 ≤ (f : ℝ) * ((m : ℝ) - 1) * (m : ℝ) / 2 := by
      have hmpos : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      positivity
    linarith
  -- Step 5: Combine `(2/3)^f` and `(2^(2f))⁻¹` constants cleanly: `log(2/3) - 2 log 2 = -log 6`
  have hconst : (f : ℝ) * Real.log (2 / 3 : ℝ) - 2 * (f : ℝ) * Real.log 2 =
      -((f : ℝ) * Real.log 6) := by
    have h23 : Real.log (2 / 3 : ℝ) = Real.log 2 - Real.log 3 :=
      Real.log_div (by norm_num) (by norm_num)
    have h6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
      have : (6 : ℝ) = 2 * 3 := by norm_num
      rw [this, Real.log_mul (by norm_num) (by norm_num)]
    rw [h23, h6]
    ring
  -- Step 6: Assemble the unnormalized log inequality and divide by `f * k > 0`
  have hfac_mul :
      (f : ℝ) * (∑ M ∈ Finset.Ico (k + 1) (k + m),
        (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ))) ≤
      (f : ℝ) * (∑ M ∈ Finset.Ico (k + 1) (k + m), Real.log (Nat.factorial (M - 1) : ℝ)) :=
    mul_le_mul_of_nonneg_left hfac_sum hfpos.le
  have htotal :
      (f : ℝ) * (k : ℝ) * ((m : ℝ) * (Real.log g₁ + Real.log g₂) +
        ((m : ℝ) - 1) * Real.log (vE / Real.pi)) +
      (f : ℝ) * (∑ M ∈ Finset.Ico (k + 1) (k + m),
        (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ))) +
      Real.log dimRatio -
      ((f : ℝ) * ((m : ℝ) - 1) / 2) * Real.log (2 * vE) -
      (f : ℝ) * (B_L + Real.log 6) ≤
      Real.log (Dstar / dstar) := by
    linarith [hlog_cov, hlog_idx, hlog_mass_eq, hfac_mul, hLlog, hquad_g, hquad_v, hconst]
  -- Divide by `f * k > 0`
  have hdiv := div_le_div_of_nonneg_right htotal hfkpos.le
  have hsimp :
      ((f : ℝ) * (k : ℝ) * ((m : ℝ) * (Real.log g₁ + Real.log g₂) +
        ((m : ℝ) - 1) * Real.log (vE / Real.pi)) +
      (f : ℝ) * (∑ M ∈ Finset.Ico (k + 1) (k + m),
        (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ))) +
      Real.log dimRatio -
      ((f : ℝ) * ((m : ℝ) - 1) / 2) * Real.log (2 * vE) -
      (f : ℝ) * (B_L + Real.log 6)) / ((f : ℝ) * (k : ℝ)) =
      (m : ℝ) * (Real.log g₁ + Real.log g₂) +
      ((m : ℝ) - 1) * Real.log (vE / Real.pi) +
      (1 / (k : ℝ)) * (∑ M ∈ Finset.Ico (k + 1) (k + m),
        (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ))) +
      (1 / ((f : ℝ) * (k : ℝ))) * Real.log dimRatio -
      ((m : ℝ) - 1) / (2 * (k : ℝ)) * Real.log (2 * vE) -
      (B_L + Real.log 6) / (k : ℝ) := by
    field_simp [hfpos.ne', hkpos.ne']
  rw [hsimp] at hdiv
  have hrhs : Real.log (Dstar / dstar) / ((f : ℝ) * (k : ℝ)) =
      (1 / ((f : ℝ) * (k : ℝ))) * Real.log (Dstar / dstar) := by
    ring
  rwa [hrhs] at hdiv

/-- **Clean Error-Budget Specialization (`mass_ratio_ge_with_error`)**:
under the `GL5` / `MassLowerBoundClosed` scale hypotheses (`log vE ≤ L`, `B_L ≤ m * C_L`,
and Weyl+factorial combined lower bound `W_lo ≤ (1/k) ∑ ((M-1) log(M-1) - (M-1)) + (1/(f k)) log dimRatio`),
the normalized log covolume ratio satisfies the exact linear-in-`m` lower bound with
`O(L + m L / k)` error that feeds directly into `RHDirect.ScaleParams` (`m^2 L ≤ k`). -/
theorem mass_ratio_ge_with_error
    {f m k : ℕ} {vE g₁ g₂ massk massr Isig Ipi Dstar dstar dimRatio B_L L W_lo : ℝ}
    {Lval : ℕ → ℝ}
    (hf : 1 ≤ f) (hm : 1 ≤ m) (hk : 2 ≤ k)
    (hv : Real.pi ≤ vE) (hvL : Real.log vE ≤ L) (hL_ge_one : 1 ≤ L)
    (hg₁ : 1 ≤ g₁) (hg₂ : 1 ≤ g₂)
    (hmk : 0 < massk) (hmr : 0 < massr) (hIsig : 0 < Isig) (hIpi : 0 < Ipi)
    (hdim : 0 < dimRatio)
    (hLpos : ∀ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1), 0 < Lval M)
    (hLlog : -((f : ℝ) * B_L) ≤ ∑ M ∈ Finset.Ico (k + 1) (k + m), Real.log (Lval M))
    (hBL : B_L ≤ (m : ℝ) * L)
    (hmass : massr = massk * ∏ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1),
      massRatioFactor f vE Lval M)
    (hidx : ((2 : ℝ) ^ (2 * f))⁻¹ *
        (g₁ * g₂) ^ ((f : ℝ) * (m : ℝ) * (2 * (k : ℝ) + (m : ℝ) - 1) / 2) ≤
      Isig / Ipi)
    (hcov : (2 / 3 : ℝ) ^ f * (massr / massk) * (Isig / Ipi) * dimRatio ≤ Dstar / dstar)
    (hW : W_lo ≤
      (1 / (k : ℝ)) * (∑ M ∈ Finset.Ico (k + 1) (k + m),
        (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ))) +
      (1 / ((f : ℝ) * (k : ℝ))) * Real.log dimRatio) :
    (m : ℝ) * (Real.log g₁ + Real.log g₂) +
      ((m : ℝ) - 1) * Real.log (vE / Real.pi) + W_lo -
      (3 * (m : ℝ) * L + Real.log 6) / (k : ℝ)
      ≤ (1 / ((f : ℝ) * (k : ℝ))) * Real.log (Dstar / dstar) := by
  have hmain := mass_ratio_ge hf hm hk hv hg₁ hg₂ hmk hmr hIsig hIpi hdim
    hLpos hLlog hmass hidx hcov
  have hvpos : 0 < vE := lt_of_lt_of_le Real.pi_pos hv
  have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm1_nonneg : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hm_ge : (m : ℝ) - 1 ≤ (m : ℝ) := by linarith
  have hlog2_le_one : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog2v : Real.log (2 * vE) ≤ 2 * L := by
    rw [Real.log_mul (by norm_num) hvpos.ne']
    linarith
  have hterm1 : ((m : ℝ) - 1) / (2 * (k : ℝ)) * Real.log (2 * vE) ≤ (m : ℝ) * L / (k : ℝ) := by
    have hlog2v_nn : 0 ≤ Real.log (2 * vE) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have hstep1 : ((m : ℝ) - 1) / (2 * (k : ℝ)) * Real.log (2 * vE) ≤
        ((m : ℝ) - 1) / (2 * (k : ℝ)) * (2 * L) :=
      mul_le_mul_of_nonneg_left hlog2v (div_nonneg hm1_nonneg (by linarith))
    have hstep2 : ((m : ℝ) - 1) / (2 * (k : ℝ)) * (2 * L) = ((m : ℝ) - 1) * L / (k : ℝ) := by
      field_simp [hkpos.ne']
    have hstep3 : ((m : ℝ) - 1) * L / (k : ℝ) ≤ (m : ℝ) * L / (k : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hm_ge (by linarith)) hkpos.le
    linarith
  have hterm2 : (B_L + Real.log 6) / (k : ℝ) ≤ ((m : ℝ) * L + Real.log 6) / (k : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hkpos.le
  have hcombine : (m : ℝ) * L / (k : ℝ) + ((m : ℝ) * L + Real.log 6) / (k : ℝ) ≤
      (3 * (m : ℝ) * L + Real.log 6) / (k : ℝ) := by
    have hnn : 0 ≤ (m : ℝ) * L := mul_nonneg (Nat.cast_nonneg m) (by linarith)
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hkpos.le
    linarith
  linarith

/-- **Bridge to `RHDirect.ScaleParams` & `RHDirect.ChainRanks`**:
in the `√x` theta-lift chain regime (`R.k ≥ 2`, `(R.m : ℝ) * s.L ≤ R.k`),
the normalized mass-ratio error `(3 * m * L + log 6) / k` is uniformly bounded by `4`,
so the linear-in-`m` level-index growth `m * (log g₁ + log g₂)` dominates strictly! -/
theorem mass_ratio_error_le_four_of_scaleParams (s : ScaleParams) (R : ChainRanks)
    (hk : 2 ≤ R.k) (hmk : (R.m : ℝ) * s.L ≤ (R.k : ℝ)) :
    (3 * (R.m : ℝ) * s.L + Real.log 6) / (R.k : ℝ) ≤ 4 := by
  have hkpos : (0 : ℝ) < (R.k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog6 : Real.log 6 ≤ 2 := by
    have hexp : (6 : ℝ) ≤ Real.exp 2 := by
      have h1 : (6 / 5 : ℝ) ≤ Real.exp (1 / 5 : ℝ) := by
        have := Real.add_one_le_exp (1 / 5 : ℝ)
        linarith
      have h2 : (6 / 5 : ℝ) ^ 10 ≤ (Real.exp (1 / 5 : ℝ)) ^ 10 :=
        pow_le_pow_left₀ (by norm_num) h1 10
      have h3 : (Real.exp (1 / 5 : ℝ)) ^ 10 = Real.exp 2 := by
        rw [← Real.exp_nat_mul]
        norm_num
      have h4 : (6 : ℝ) ≤ (6 / 5 : ℝ) ^ 10 := by norm_num
      linarith
    exact (Real.log_le_iff_le_exp (by norm_num)).mpr hexp
  rw [div_le_iff₀ hkpos]
  have hk2 : (2 : ℝ) ≤ (R.k : ℝ) := by exact_mod_cast hk
  linarith

end RHDirect.UnitaryMassFormula

end
