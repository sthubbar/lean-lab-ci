/-
P0087 Akeno 2026 elementary facts used in Lemma 4.6 on page 34.
Quadratic residue classes, their Legendre symbol count and prime density bounds.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.Statements

namespace LeanLab.Akeno2026.QuadraticSieve
open Finset

/-- The paper's residue set Omega_N(d). -/
def omegaResidues (N : ℤ) (d : ℕ) : Set (ZMod d) :=
  {x | 2 * x * ((N : ZMod d) - x) + 1 = 0}
noncomputable def omegaCount (N : ℤ) (d : ℕ) : ℕ := Nat.card (omegaResidues N d)
/-- The page 34 local density, with the explicit zero value for even d. -/
noncomputable def gDensity (N d : ℕ) : ℝ :=
  if Even d then 0 else (omegaCount (N : ℤ) d : ℝ) / psiN N d

theorem quad_admissible {d l N : ℤ} (h : d ∣ 2 * l * (N - l) + 1) :
    IsCoprime d (l * (N - l)) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, -2, by nlinarith⟩

theorem quad_coprime_factors {d l N : ℤ} (h : d ∣ 2 * l * (N - l) + 1) :
    IsCoprime d l ∧ IsCoprime d (N - l) :=
  IsCoprime.mul_right_iff.mp (quad_admissible h)

/-- The discriminant change of variables used on page 34. -/
theorem quad_square_iff {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (N x : K) :
    2 * x * (N - x) + 1 = 0 ↔ (2 * x - N) ^ 2 = N ^ 2 + 2 := by
  constructor
  · intro h
    linear_combination -2 * h
  · intro h
    have he : (2 : K) * (2 * x * (N - x) + 1) = 0 := by linear_combination -h
    exact (mul_eq_zero.mp he).resolve_left h2

theorem two_ne_zero_mod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact (Fact.out : p.Prime).ne_one h1
  · exact hp h2

/-- The exact Legendre symbol formula for the number of root classes. -/
theorem omegaCount_eq_legendre (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (N : ℤ) :
    (omegaCount N p : ℤ) = legendreSym p (N ^ 2 + 2) + 1 := by
  classical
  have h2 := two_ne_zero_mod hp
  let S : Finset (ZMod p) := (omegaResidues N p).toFinset
  let T : Finset (ZMod p) := {y : ZMod p | y ^ 2 = (N ^ 2 + 2 : ℤ)}.toFinset
  have hc : S.card = T.card := by
    apply Finset.card_bij (fun x _ => 2 * x - (N : ZMod p))
    · intro x hx
      have hx' : 2 * x * ((N : ZMod p) - x) + 1 = 0 := (Set.mem_toFinset.mp hx : x ∈ omegaResidues N p)
      change (2 * x - (N : ZMod p)) ∈ T
      simp only [T, Set.mem_toFinset, Set.mem_ofPred_eq]
      push_cast
      exact (quad_square_iff h2 (N : ZMod p) x).mp hx'
    · intro x _ y _ hxy
      have he : (2 : ZMod p) * x = 2 * y := by linear_combination hxy
      exact mul_left_cancel₀ h2 he
    · intro y hy
      have he : 2 * ((y + (N : ZMod p)) / 2) - (N : ZMod p) = y := by
        field_simp [h2]
        ring
      refine ⟨(y + (N : ZMod p)) / 2, ?_, he⟩
      apply Set.mem_toFinset.mpr
      change 2 * ((y + (N : ZMod p)) / 2) * ((N : ZMod p) - (y + (N : ZMod p)) / 2) + 1 = 0
      apply (quad_square_iff h2 (N : ZMod p) _).mpr
      rw [he]
      have hy' : y ^ 2 = ((N ^ 2 + 2 : ℤ) : ZMod p) := by simpa [T] using hy
      push_cast at hy'
      exact hy'
  have hS : S.card = omegaCount N p := by
    simp [S, omegaCount, Set.toFinset_card, Nat.card_eq_fintype_card]
  calc
    (omegaCount N p : ℤ) = (T.card : ℤ) := by exact_mod_cast (hS.symm.trans hc)
    _ = legendreSym p (N ^ 2 + 2) + 1 := legendreSym.card_sqrts p hp _

theorem omegaCount_le_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (N : ℤ) :
    omegaCount N p ≤ 2 := by
  have h := omegaCount_eq_legendre p hp N
  have hl : legendreSym p (N ^ 2 + 2) ≤ 1 := by
    unfold legendreSym
    simp only [quadraticChar_apply]
    unfold quadraticCharFun
    split_ifs <;> norm_num
  have h' : (omegaCount N p : ℤ) ≤ 2 := by linarith
  exact_mod_cast h'

theorem omega_three_empty (N : ℤ) (hN : 3 ∣ N) : omegaResidues N 3 = ∅ := by
  have h0 : (N : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd N 3).mpr hN
  have h : ∀ x : ZMod 3, 2 * x * (0 - x) + 1 ≠ 0 := by decide +kernel
  ext x
  change (2 * x * ((N : ZMod 3) - x) + 1 = 0) ↔ False
  rw [h0]
  exact iff_false_intro (h x)

theorem omegaCount_three (N : ℤ) (hN : 3 ∣ N) : omegaCount N 3 = 0 := by
  simp [omegaCount, omega_three_empty N hN]

theorem gDensity_three (N : ℕ) (hN : 3 ∣ N) : gDensity N 3 = 0 := by
  have hz : omegaCount (N : ℤ) 3 = 0 := omegaCount_three N (by exact_mod_cast hN)
  norm_num [gDensity, hz]

theorem gDensity_two (N : ℕ) : gDensity N 2 = 0 := by norm_num [gDensity]

theorem gDensity_bounds (N p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    0 ≤ gDensity N p ∧ gDensity N p ≤ 2 / ((p : ℝ) - 2) := by
  let : Fact p.Prime := ⟨hp⟩
  have hP : (5 : ℝ) ≤ p := by exact_mod_cast h5
  have hden : (p : ℝ) - 2 ≤ psiN N p := by
    by_cases h : p ∣ N
    · rw [psiN_prime_dvd hp h]
      linarith
    · rw [psiN_prime_not_dvd hp h]
  have hden0 : 0 < psiN N p := by linarith
  have hc : (omegaCount (N : ℤ) p : ℝ) ≤ 2 := by
    exact_mod_cast omegaCount_le_two p (by omega) (N : ℤ)
  by_cases he : Even p
  · rw [gDensity, ite_eq_left he]
    exact ⟨le_rfl, div_nonneg (by norm_num) (by linarith)⟩
  · rw [gDensity, ite_eq_right he]
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hden0.le
    · calc
        (omegaCount (N : ℤ) p : ℝ) / psiN N p ≤ 2 / psiN N p :=
          div_le_div_of_nonneg_right hc hden0.le
        _ ≤ 2 / ((p : ℝ) - 2) := div_le_div_of_nonneg_left (by norm_num) (by linarith) hden

theorem local_factor_bounds (N p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    (1 / 3 : ℝ) ≤ 1 - gDensity N p ∧ 1 - gDensity N p ≤ 1 := by
  obtain ⟨h0, h1⟩ := gDensity_bounds N p hp h5
  have hP : (5 : ℝ) ≤ p := by exact_mod_cast h5
  have he : 2 / ((p : ℝ) - 2) ≤ 2 / 3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  constructor <;> linarith

end LeanLab.Akeno2026.QuadraticSieve
