/- AI wrote this Lean code for CODEX task148.
Recovered from this run's recorded write commands after execution access failed.
Fresh build, seal and branch checks are required. Goldbach is open. -/
import LeanLab.BS2022GRH.ChenThresholdGRH
import LeanLab.BS2022GRH.CharacterC164
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
namespace LeanLab.BS2022GRH.Decomp148a
open Real Finset Classical ChenThresholdGRH
noncomputable section
/-- Positive integer indices n < X, journal p. 1222. -/
def nRange (X : ℝ) : Finset ℕ := Ico 1 ⌈X⌉₊
/-- Prime indices Z ≤ p < Y, journal p. 1222. -/
def pRange (Y Z : ℝ) : Finset ℕ :=
  (range ⌈Y⌉₊).filter (fun p => p.Prime ∧ Z ≤ (p : ℝ))
/-- The discrepancy inside display 11. -/
def discrepancy (c : ℕ → ℂ) (X Y Z : ℝ) (d b : ℕ) : ℂ :=
  (∑ n ∈ nRange X, ∑ p ∈ (pRange Y Z).filter (fun p => (n * p) % d = b % d), c n)
    - (d.totient : ℂ)⁻¹ *
      ∑ n ∈ nRange X, ∑ p ∈ (pRange Y Z).filter (fun p => Nat.Coprime (n * p) d), c n
/-- Maximum over reduced residues, display 11. -/
def maxDiscrepancy (c : ℕ → ℂ) (X Y Z : ℝ) (d : ℕ) : ℝ :=
  ↑(((range d).filter (fun b => Nat.Coprime b d)).sup
    (fun b => (⟨‖discrepancy c X Y Z d b‖, norm_nonneg _⟩ : NNReal)))
/-- Squarefree moduli with the outer coprimality restriction, display 11. -/
def moduli (D : ℝ) (a : ℤ) : Finset ℕ :=
  (Ico 1 ⌈D⌉₊).filter (fun d => Squarefree d ∧ Nat.Coprime a.natAbs d)
/-- Complete left side of display 11. -/
def bilinear (c : ℕ → ℂ) (X Y Z D : ℝ) (a : ℤ) : ℝ :=
  ∑ d ∈ moduli D a, maxDiscrepancy c X Y Z d
/-- Primitive-character product in display 12. -/
def primitiveTerm (c : ℕ → ℂ) (X Y Z : ℝ) (r s : ℕ) : ℝ :=
  ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive),
    ‖∑ n ∈ (nRange X).filter (fun n => Nat.Coprime n s), c n * χ n‖ *
    ‖∑ p ∈ (pRange Y Z).filter (fun p => ¬ p ∣ s), χ p‖
/-- Conductor range, display 12 and p. 1224. -/
def conductors (D : ℝ) (a : ℤ) : Finset ℕ :=
  (Ico 3 ⌈D⌉₊).filter (fun r => Squarefree r ∧ Nat.Coprime a.natAbs r)
/-- Weighted conductor contribution in display 12. -/
def conductorTerm (c : ℕ → ℂ) (X Y Z D : ℝ) (a : ℤ) (r : ℕ) : ℝ :=
  (r.totient : ℝ)⁻¹ * ∑ s ∈ moduli (D / r) a,
    (s.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s
/-- Small-conductor contribution in display 13. -/
def smallMass (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (a : ℤ) : ℝ :=
  ∑ r ∈ (conductors D a).filter (fun r : ℕ => (r : ℝ) ≤ D₀), conductorTerm c X Y Z D a r
/-- Complementary large-conductor contribution, displays 14 and 16. -/
def largeMass (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (a : ℤ) : ℝ :=
  ∑ r ∈ (conductors D a).filter (fun r : ℕ => D₀ < (r : ℝ)), conductorTerm c X Y Z D a r
/-- Normalizing factor in displays 17 and 18. -/
def scale (X Y D : ℝ) : ℝ := D * √(X * Y) * log D ^ 2
/-- Chosen splitting point, journal p. 1226. -/
def cutoff (Y : ℝ) : ℝ := (√Y / (2 * log 2 * qG Y * log Y)) ^ (1 / 3 : ℝ)
/-- Right side of display 13. -/
def smallBound (X Y D D₀ : ℝ) : ℝ :=
  Mphi D₀ * Mphi D * D₀ * X * log D ^ 2 *
    (1.3841 * log D / log (log D) + 2 * D₀ + 2 * D₀ * qG Y * √Y * log Y)
/-- Right side of display 16. -/
def largeBound (X Y D D₀ : ℝ) : ℝ :=
  Mphi D / log 2 * log D ^ 2 *
    (4 * D * √(X * Y) + 2 * (√X + √Y) * √(X * Y) + X * Y / D₀)
/-- Common normalized term in displays 17 and 18. -/
def balance (X Y D : ℝ) : ℝ :=
  qG Y ^ (1 / 3 : ℝ) * (2 * log 2) ^ (-(2 / 3) : ℝ) *
    (X ^ (1 / 2 : ℝ) * Y ^ (1 / 3 : ℝ) * log Y ^ (1 / 3 : ℝ) / D)
/-- Right side of display 17. -/
def smallCoeff (X Y D : ℝ) : ℝ :=
  2 * Mphi0 Y * Mphi D *
    (balance X Y D + (2 * qG Y * log 2) ^ (-(2 / 3) : ℝ) *
      (X ^ (1 / 2 : ℝ) / (Y ^ (1 / 6 : ℝ) * D * log Y ^ (2 / 3 : ℝ))) +
      0.69205 * (2 * qG Y * log 2) ^ (-(1 / 3) : ℝ) *
      (X ^ (1 / 2 : ℝ) * log D /
        (Y ^ (1 / 3 : ℝ) * D * log (log D) * log Y ^ (1 / 3 : ℝ))))
/-- Right side of display 18. -/
def largeCoeff (X Y D : ℝ) : ℝ :=
  2 * Mphi D * (2 / log 2 + balance X Y D + (√X + √Y) / (D * log 2))
/-- Coefficient m of Lemma 8, split as displays 17 and 18. -/
def mJ (X Y D : ℝ) : ℝ := smallCoeff X Y D + largeCoeff X Y D
/-- Lemma 8, display 11. New paper Prop requiring Claude review.
The unsubscripted maximum is interpreted over reduced residues for each modulus. -/
def Lemma8J : Prop :=
  GRH → ∀ (c : ℕ → ℂ) (X Y Z D : ℝ) (a : ℤ), (∀ n, ‖c n‖ ≤ 1) →
    25 ≤ X → 25 ≤ Y → 25 ≤ Z → Z < Y → 1 < D → D < √(X * Y) →
    √(X * Y) / D ≤ cutoff Y → cutoff Y ≤ min D (√Z) → Even a →
    bilinear c X Y Z D a ≤ mJ X Y D * scale X Y D
/-- LEAF. Orthogonality step, p. 1223 before display 12.
Use DirichletCharacter.sum_char_inv_mul_char_eq and remove the principal character. -/
theorem orthogonality_bound (c : ℕ → ℂ) (X Y Z : ℝ) (d b : ℕ)
    (hd : 0 < d) (hb : Nat.Coprime b d) :
    ‖discrepancy c X Y Z d b‖ ≤ (d.totient : ℝ)⁻¹ *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ ≠ 1),
        ‖∑ n ∈ nRange X, c n * χ n‖ * ‖∑ p ∈ pRange Y Z, χ p‖ := by
  exact CharacterC164.error_norm_le (nRange X) (pRange Y Z) c d b hd hb
private lemma char_apply_eq_zero {r : ℕ} (ψ : DirichletCharacter ℂ r) {n : ℕ}
    (h : ¬ Nat.Coprime n r) : ψ (n : ZMod r) = 0 := by
  apply MulChar.map_nonunit
  rwa [ZMod.isUnit_iff_coprime]

private lemma changeLevel_apply_nat {r m : ℕ} (ψ : DirichletCharacter ℂ r) (hm : r ∣ m) (a : ℕ) :
    (DirichletCharacter.changeLevel hm ψ) (a : ZMod m) =
      if Nat.Coprime a m then ψ (a : ZMod r) else 0 := by
  have hcast : ((a : ℕ) : ZMod m) = ((a : ℤ) : ZMod m) := by push_cast; ring
  by_cases h : Nat.Coprime a m
  · rw [if_pos h, hcast, DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hm h.isCoprime]
    push_cast; ring
  · rw [if_neg h, hcast]
    apply MulChar.map_nonunit
    rw [← hcast, ZMod.isUnit_iff_coprime]
    exact h

private lemma coprime_of_coprime_mul_left {n r s : ℕ} (h : Nat.Coprime n (r * s)) :
    Nat.Coprime n r := h.coprime_dvd_right ⟨s, rfl⟩
private lemma coprime_of_coprime_mul_right {n r s : ℕ} (h : Nat.Coprime n (r * s)) :
    Nat.Coprime n s := h.coprime_dvd_right ⟨r, by ring⟩

private lemma not_coprime_of_not_coprime_mul {n r s : ℕ} (h : ¬ Nat.Coprime n (r * s))
    (hs : Nat.Coprime n s) : ¬ Nat.Coprime n r := fun hr => h (hr.mul_right hs)
private lemma not_coprime_mul_of_not_coprime {n r s : ℕ} (h : ¬ Nat.Coprime n s) :
    ¬ Nat.Coprime n (r * s) := fun hr => h (coprime_of_coprime_mul_right hr)

private lemma sum_n_changeLevel {r m : ℕ} (ψ : DirichletCharacter ℂ r) (hm : r ∣ m) (s : ℕ)
    (hms : m = r * s) (c : ℕ → ℂ) (X : ℝ) :
    ∑ n ∈ nRange X, c n * (DirichletCharacter.changeLevel hm ψ) (n : ZMod m) =
      ∑ n ∈ (nRange X).filter (fun n => Nat.Coprime n s), c n * ψ (n : ZMod r) := by
  have key : ∀ n : ℕ, c n * (DirichletCharacter.changeLevel hm ψ) (n : ZMod m) =
      if Nat.Coprime n s then c n * ψ (n : ZMod r) else 0 := by
    intro n
    rw [changeLevel_apply_nat ψ hm n, hms]
    by_cases hns : Nat.Coprime n s
    · rw [if_pos hns]
      by_cases hnm : Nat.Coprime n (r * s)
      · rw [if_pos hnm]
      · rw [if_neg hnm, mul_zero, char_apply_eq_zero ψ (not_coprime_of_not_coprime_mul hnm hns),
          mul_zero]
    · rw [if_neg hns]
      rw [if_neg (not_coprime_mul_of_not_coprime hns), mul_zero]
  rw [Finset.sum_congr rfl (fun n _ => key n), Finset.sum_filter]

private lemma sum_p_changeLevel {r m : ℕ} (ψ : DirichletCharacter ℂ r) (hm : r ∣ m) (s : ℕ)
    (hms : m = r * s) (Y Z : ℝ) :
    ∑ p ∈ pRange Y Z, (DirichletCharacter.changeLevel hm ψ) (p : ZMod m) =
      ∑ p ∈ (pRange Y Z).filter (fun p => ¬ p ∣ s), ψ (p : ZMod r) := by
  have key : ∀ p ∈ pRange Y Z,
      (DirichletCharacter.changeLevel hm ψ) (p : ZMod m) =
        if ¬ p ∣ s then ψ (p : ZMod r) else 0 := by
    intro p hp
    obtain ⟨-, hpp, -⟩ := Finset.mem_filter.mp hp
    have h1 : 1 < p := hpp.one_lt
    rw [changeLevel_apply_nat ψ hm p, hms]
    by_cases hps : p ∣ s
    · rw [if_neg (Nat.not_coprime_of_dvd_of_dvd h1 (dvd_refl p) (hps.trans ⟨r, by ring⟩)),
        if_neg (fun hq => hq hps)]
    · rw [if_pos hps]
      have hpsc : Nat.Coprime p s := hpp.coprime_iff_not_dvd.mpr hps
      by_cases hpm : Nat.Coprime p (r * s)
      · rw [if_pos hpm]
      · rw [if_neg hpm, char_apply_eq_zero ψ (fun hpr => hpm (hpr.mul_right hpsc))]
  calc ∑ p ∈ pRange Y Z, (DirichletCharacter.changeLevel hm ψ) (p : ZMod m)
      = ∑ p ∈ pRange Y Z, if ¬ p ∣ s then ψ (p : ZMod r) else 0 :=
        Finset.sum_congr rfl key
    _ = _ := by rw [Finset.sum_filter]


/-- Step 1: each modulus is controlled by its nonprincipal character expansion. -/
private lemma maxDiscrepancy_le (c : ℕ → ℂ) (X Y Z : ℝ) (d : ℕ) (hd : 0 < d) :
    maxDiscrepancy c X Y Z d ≤ (d.totient : ℝ)⁻¹ *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ ≠ 1),
        ‖∑ n ∈ nRange X, c n * χ n‖ * ‖∑ p ∈ pRange Y Z, χ p‖ := by
  classical
  letI : DecidableEq (DirichletCharacter ℂ d) := Classical.decEq _
  set B : ℝ := (d.totient : ℝ)⁻¹ *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ ≠ 1),
        ‖∑ n ∈ nRange X, c n * χ n‖ * ‖∑ p ∈ pRange Y Z, χ p‖ with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg ?_)
    intro χ _
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hcoe : (((range d).filter (fun b => Nat.Coprime b d)).sup
      (fun b => (⟨‖discrepancy c X Y Z d b‖, norm_nonneg _⟩ : NNReal))) ≤ ⟨B, hB0⟩ := by
    refine Finset.sup_le ?_
    intro b hb
    obtain ⟨-, hb2⟩ := Finset.mem_filter.mp hb
    exact CharacterC164.error_norm_le (nRange X) (pRange Y Z) c d b hd hb2
  exact NNReal.coe_le_coe.mpr hcoe


/-- `2` divides the absolute value of an even integer. -/
private lemma two_dvd_natAbs_of_even {a : ℤ} (ha : Even a) : 2 ∣ a.natAbs :=
  even_iff_two_dvd.mp (Int.natAbs_even.mpr ha)

/-- An even `a` coprime to `d` forces `d` to be odd. -/
private lemma not_two_dvd_of_even_of_coprime {a : ℤ} (ha : Even a) {d : ℕ}
    (hcop : Nat.Coprime a.natAbs d) : ¬ 2 ∣ d := by
  intro h2
  have h1 : Nat.gcd a.natAbs d = 1 := hcop
  have h := Nat.dvd_gcd (two_dvd_natAbs_of_even ha) h2
  rw [h1] at h
  norm_num at h

/-- A nonprincipal character of odd level has conductor at least `3`. -/
private lemma three_le_conductor {d : ℕ} (χ : DirichletCharacter ℂ d) (hd : 0 < d)
    (hne : χ ≠ 1) (hodd : ¬ 2 ∣ d) : 3 ≤ χ.conductor := by
  haveI : NeZero d := ⟨Nat.pos_iff_ne_zero.mp hd⟩
  have hrne1 : χ.conductor ≠ 1 := fun h =>
    hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
  have hrne0 : χ.conductor ≠ 0 := DirichletCharacter.conductor_ne_zero χ
  have hdvd : χ.conductor ∣ d := DirichletCharacter.conductor_dvd_level χ
  have hrodd : ¬ 2 ∣ χ.conductor := fun h => hodd (h.trans hdvd)
  have hodd' : Odd χ.conductor := Nat.not_even_iff_odd.mp (fun he => hrodd (even_iff_two_dvd.mp he))
  obtain ⟨k, hk⟩ := hodd'
  omega

/-- Ceiling arithmetic: a divisor quotient stays inside the reduced ceiling. -/
private lemma div_lt_ceil_div {D : ℝ} {d r s : ℕ} (hrs : d = r * s) (hr0 : 0 < r)
    (hdlt : d < ⌈D⌉₊) : s < ⌈D / r⌉₊ := by
  have hdD : (d : ℝ) < D := Nat.lt_ceil.mp hdlt
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hsr : (s : ℝ) < D / r := by
    rw [lt_div_iff₀ hr0']
    calc (s : ℝ) * r = (d : ℝ) := by rw [hrs]; push_cast; ring
      _ < D := hdD
  have hle : D / r ≤ ((⌈D / r⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : (s : ℝ) < ((⌈D / r⌉₊ : ℕ) : ℝ) := lt_of_lt_of_le hsr hle
  exact_mod_cast h2

/-- The totient of a product of coprime factors splits the inverse weight. -/
private lemma totient_inv_mul {r s d : ℕ} (hrs : d = r * s) (hcop : Nat.Coprime r s) :
    ((d.totient : ℝ))⁻¹ = ((r.totient : ℝ))⁻¹ * ((s.totient : ℝ))⁻¹ := by
  rw [hrs, Nat.totient_mul hcop]
  push_cast
  rw [mul_inv]

/-- The two character sums of display 12 agree at a pair of complementary levels. -/
private lemma norm_factors_eq {r d s : ℕ} (ψ : DirichletCharacter ℂ r) (hm : r ∣ d)
    (hms : d = r * s) (c : ℕ → ℂ) (X Y Z : ℝ) :
    ‖∑ n ∈ nRange X, c n * (DirichletCharacter.changeLevel hm ψ) (n : ZMod d)‖ *
        ‖∑ p ∈ pRange Y Z, (DirichletCharacter.changeLevel hm ψ) (p : ZMod d)‖ =
      ‖∑ n ∈ (nRange X).filter (fun n => Nat.Coprime n s), c n * ψ (n : ZMod r)‖ *
        ‖∑ p ∈ (pRange Y Z).filter (fun p => ¬ p ∣ s), ψ (p : ZMod r)‖ := by
  rw [sum_n_changeLevel ψ hm s hms c X, sum_p_changeLevel ψ hm s hms Y Z]


/-- Characters of a positive level agreeing on all natural numbers coincide. -/
private lemma dirichlet_ext_nat {d : ℕ} [NeZero d] {χ χ' : DirichletCharacter ℂ d}
    (h : ∀ n : ℕ, χ (n : ZMod d) = χ' (n : ZMod d)) : χ = χ' := by
  refine MulChar.ext ?_
  intro u
  rw [← ZMod.natCast_zmod_val (u : ZMod d)]
  exact h _

/-- LEAF. Primitive conductor reduction, display 12 p. 1223.
Use the orthogonality bound and primitiveCharacter_isPrimitive.
Squarefree weights become support conditions. -/
theorem primitive_reduction (c : ℕ → ℂ) (X Y Z D : ℝ) (a : ℤ)
    (hD : 1 < D) (ha : Even a) :
    bilinear c X Y Z D a ≤ ∑ r ∈ conductors D a, conductorTerm c X Y Z D a r := by

  classical
  have hstep : bilinear c X Y Z D a ≤
      ∑ d ∈ moduli D a, (d.totient : ℝ)⁻¹ *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ ≠ 1),
          ‖∑ n ∈ nRange X, c n * χ n‖ * ‖∑ p ∈ pRange Y Z, χ p‖ := by
    rw [bilinear]
    refine Finset.sum_le_sum ?_
    intro d hd
    obtain ⟨hIco, -⟩ := Finset.mem_filter.mp hd
    exact maxDiscrepancy_le c X Y Z d (Finset.mem_Ico.mp hIco).1
  set F : (d : ℕ) → Finset (DirichletCharacter ℂ d) :=
    fun d => (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ ≠ 1) with hF
  set SL : Finset ((d : ℕ) × DirichletCharacter ℂ d) := (moduli D a).sigma F with hSL
  set hL : ((d : ℕ) × DirichletCharacter ℂ d) → ℝ := fun x =>
    (x.1.totient : ℝ)⁻¹ *
      (‖∑ n ∈ nRange X, c n * x.2 n‖ * ‖∑ p ∈ pRange Y Z, x.2 p‖) with hhL
  set G : (r : ℕ) → Finset ((s : ℕ) × DirichletCharacter ℂ r) := fun r =>
    (moduli (D / r) a).sigma (fun s =>
      (univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.IsPrimitive)) with hG
  set SR : Finset ((r : ℕ) × (s : ℕ) × DirichletCharacter ℂ r) := (conductors D a).sigma G with hSR
  set gg : ((r : ℕ) × (s : ℕ) × DirichletCharacter ℂ r) → ℝ := fun y =>
    (y.1.totient : ℝ)⁻¹ * ((y.2.1.totient : ℝ)⁻¹ *
      (‖∑ n ∈ (nRange X).filter (fun n => Nat.Coprime n y.2.1), c n * y.2.2 n‖ *
       ‖∑ p ∈ (pRange Y Z).filter (fun p => ¬ p ∣ y.2.1), y.2.2 p‖)) with hgg
  set Φ : ((d : ℕ) × DirichletCharacter ℂ d) → ((r : ℕ) × (s : ℕ) × DirichletCharacter ℂ r) :=
    fun x => ⟨x.2.conductor, x.1 / x.2.conductor, x.2.primitiveCharacter⟩ with hΦ
  -- non-dependent triples, which avoid dependent elimination in the reindexing
  set Φtr : ((d : ℕ) × DirichletCharacter ℂ d) → (ℕ × ℕ × (ℕ → ℂ)) := fun x =>
    (x.2.conductor, x.1 / x.2.conductor,
      fun n => x.2.primitiveCharacter (n : ZMod x.2.conductor)) with hΦtr
  set Ψtr : ((r : ℕ) × (s : ℕ) × DirichletCharacter ℂ r) → (ℕ × ℕ × (ℕ → ℂ)) := fun y =>
    (y.1, y.2.1, fun n => y.2.2 (n : ZMod y.1)) with hΨtr
  set gg' : (ℕ × ℕ × (ℕ → ℂ)) → ℝ := fun t =>
    (t.1.totient : ℝ)⁻¹ * ((t.2.1.totient : ℝ)⁻¹ *
      (‖∑ n ∈ (nRange X).filter (fun n => Nat.Coprime n t.2.1), c n * t.2.2 n‖ *
       ‖∑ p ∈ (pRange Y Z).filter (fun p => ¬ p ∣ t.2.1), t.2.2 p‖)) with hgg'
  have key : ∀ x ∈ SL, x.1 ∈ moduli D a ∧ x.2 ≠ 1 ∧ x.2.conductor ∣ x.1 ∧
      0 < x.1 ∧ x.1 < ⌈D⌉₊ ∧ Squarefree x.1 ∧ 3 ≤ x.2.conductor := by
    rintro ⟨d, χ⟩ hx
    obtain ⟨hdmod, hxF⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hIco, hdsq, hdcop⟩ := Finset.mem_filter.mp hdmod
    obtain ⟨-, hχne⟩ := Finset.mem_filter.mp hxF
    exact ⟨hdmod, hχne, DirichletCharacter.conductor_dvd_level χ, (Finset.mem_Ico.mp hIco).1,
      (Finset.mem_Ico.mp hIco).2, hdsq,
      three_le_conductor χ (Finset.mem_Ico.mp hIco).1 hχne
        (not_two_dvd_of_even_of_coprime ha hdcop)⟩
  have hSN : (∑ d ∈ moduli D a, (d.totient : ℝ)⁻¹ *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ ≠ 1),
          ‖∑ n ∈ nRange X, c n * χ n‖ * ‖∑ p ∈ pRange Y Z, χ p‖) = ∑ x ∈ SL, hL x := by
    rw [hSL, Finset.sum_sigma]
    refine Finset.sum_congr rfl ?_
    intro d _
    simp only [hhL, hF]
    rw [Finset.mul_sum]
  have hRN : (∑ r ∈ conductors D a, conductorTerm c X Y Z D a r) = ∑ y ∈ SR, gg y := by
    rw [hSR, Finset.sum_sigma]
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [hG, Finset.sum_sigma, conductorTerm, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro s _
    rw [primitiveTerm, Finset.mul_sum, Finset.mul_sum]
  have hval : ∀ x ∈ SL, hL x = gg' (Φtr x) := by
    rintro ⟨d, χ⟩ hx
    obtain ⟨-, hχne, hrdvd, hdpos, hdlt, hdsq, -⟩ := key ⟨d, χ⟩ hx
    have hrpos : 0 < χ.conductor := Nat.pos_of_dvd_of_pos hrdvd hdpos
    have hrs : d = χ.conductor * (d / χ.conductor) := by
      rw [mul_comm, Nat.div_mul_cancel hrdvd]
    have hsq : Squarefree (χ.conductor * (d / χ.conductor)) := hrs ▸ hdsq
    have hcop : Nat.Coprime χ.conductor (d / χ.conductor) := Nat.coprime_of_squarefree_mul hsq
    have hw := totient_inv_mul hrs hcop
    have hA : (∑ n ∈ nRange X, c n * χ n) =
        ∑ n ∈ nRange X, c n *
          (DirichletCharacter.changeLevel hrdvd χ.primitiveCharacter) (n : ZMod d) :=
      Finset.sum_congr rfl (fun n _ => by rw [DirichletCharacter.changeLevel_primitiveCharacter])
    have hB : (∑ p ∈ pRange Y Z, χ p) =
        ∑ p ∈ pRange Y Z,
          (DirichletCharacter.changeLevel hrdvd χ.primitiveCharacter) (p : ZMod d) :=
      Finset.sum_congr rfl (fun p _ => by rw [DirichletCharacter.changeLevel_primitiveCharacter])
    have hn := norm_factors_eq χ.primitiveCharacter hrdvd hrs c X Y Z
    simp only [hL, hgg', hΦtr]
    rw [hA, hB, hn, hw]
    try ring
  have himage : ∀ x ∈ SL, Φ x ∈ SR := by
    rintro ⟨d, χ⟩ hx
    obtain ⟨hdmod, -, hrdvd, hdpos, hdlt, hdsq, hr3⟩ := key ⟨d, χ⟩ hx
    obtain ⟨-, -, hdcop⟩ := Finset.mem_filter.mp hdmod
    have hrpos : 0 < χ.conductor := Nat.pos_of_dvd_of_pos hrdvd hdpos
    have hrs : d = χ.conductor * (d / χ.conductor) := by
      rw [mul_comm, Nat.div_mul_cancel hrdvd]
    have hslt : d / χ.conductor < ⌈D / (χ.conductor : ℝ)⌉₊ := div_lt_ceil_div hrs hrpos hdlt
    have hsdvd : d / χ.conductor ∣ d := Nat.div_dvd_of_dvd hrdvd
    simp only [hΦ, hSR, hG]
    refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hr3, ?_⟩, ?_, ?_⟩
      · exact lt_of_le_of_lt (Nat.le_of_dvd hdpos hrdvd) hdlt
      · exact hdsq.squarefree_of_dvd hrdvd
      · exact hdcop.coprime_dvd_right hrdvd
    · refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, hslt⟩, ?_, ?_⟩
        · exact Nat.div_pos (Nat.le_of_dvd hdpos hrdvd) hrpos
        · exact hdsq.squarefree_of_dvd hsdvd
        · exact hdcop.coprime_dvd_right hsdvd
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, DirichletCharacter.primitiveCharacter_isPrimitive χ⟩
  have hnonneg : ∀ t, 0 ≤ gg' t := by
    intro t
    simp only [hgg']
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (mul_nonneg
      (inv_nonneg.mpr (Nat.cast_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hinjΦ : Set.InjOn Φtr ↑SL := by
    rintro ⟨d, χ⟩ hx ⟨d', χ'⟩ hx' heq
    obtain ⟨-, hχne, hrdvd, hdpos, -, -, -⟩ := key ⟨d, χ⟩ hx
    obtain ⟨-, hχne', hrdvd', hdpos', -, -, -⟩ := key ⟨d', χ'⟩ hx'
    haveI : NeZero d := ⟨Nat.pos_iff_ne_zero.mp hdpos⟩
    have h1 : χ.conductor = χ'.conductor := by
      have := congrArg (fun t : (ℕ × ℕ × (ℕ → ℂ)) => t.1) heq
      simpa only [hΦtr] using this
    have h2 : d / χ.conductor = d' / χ'.conductor := by
      have := congrArg (fun t : (ℕ × ℕ × (ℕ → ℂ)) => t.2.1) heq
      simpa only [hΦtr] using this
    have h3 : ∀ n : ℕ, χ.primitiveCharacter (n : ZMod χ.conductor) =
        χ'.primitiveCharacter (n : ZMod χ'.conductor) := by
      have h := congrArg (fun t : (ℕ × ℕ × (ℕ → ℂ)) => t.2.2) heq
      simpa only [hΦtr] using congrFun h
    have hrs : d = χ.conductor * (d / χ.conductor) := by
      rw [mul_comm, Nat.div_mul_cancel hrdvd]
    have hrs' : d' = χ'.conductor * (d' / χ'.conductor) := by
      rw [mul_comm, Nat.div_mul_cancel hrdvd']
    have hd : d = d' := by rw [hrs, h2, h1, ← hrs']
    subst hd
    have hχ : χ = χ' := by
      refine MulChar.ext ?_
      intro u
      set n : ℕ := (u : ZMod d).val with hn
      have hnd : ((n : ℕ) : ZMod d) = (u : ZMod d) := ZMod.natCast_zmod_val _
      have hc : Nat.Coprime n d := by
        rw [← ZMod.isUnit_iff_coprime n d, hnd]
        exact u.isUnit
      conv_lhs => rw [← DirichletCharacter.changeLevel_primitiveCharacter χ]
      conv_rhs => rw [← DirichletCharacter.changeLevel_primitiveCharacter χ']
      rw [← hnd, changeLevel_apply_nat χ.primitiveCharacter hrdvd n,
        changeLevel_apply_nat χ'.primitiveCharacter hrdvd' n, if_pos hc, if_pos hc]
      exact h3 n
    subst hχ
    rfl
  have hinjΨ : Set.InjOn Ψtr ↑SR := by
    rintro ⟨r, s, ψ⟩ hy ⟨r', s', ψ'⟩ hy' heq
    have h1 : r = r' := by
      have := congrArg (fun t : (ℕ × ℕ × (ℕ → ℂ)) => t.1) heq
      simpa only [hΨtr] using this
    have h2 : s = s' := by
      have := congrArg (fun t : (ℕ × ℕ × (ℕ → ℂ)) => t.2.1) heq
      simpa only [hΨtr] using this
    have h3 : ∀ n : ℕ, ψ (n : ZMod r) = ψ' (n : ZMod r') := by
      have h := congrArg (fun t : (ℕ × ℕ × (ℕ → ℂ)) => t.2.2) heq
      simpa only [hΨtr] using congrFun h
    have hr3 : 3 ≤ r := by
      simp only [hSR, hG] at hy
      exact (Finset.mem_Ico.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp hy).1).1).1
    subst h1
    subst h2
    haveI : NeZero r := ⟨by omega⟩
    have hψ : ψ = ψ' := by
      apply dirichlet_ext_nat
      intro n
      exact h3 n
    subst hψ
    rfl
  have hsub : SL.image Φtr ⊆ SR.image Ψtr := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    refine Finset.mem_image.mpr ⟨Φ x, himage x hx, ?_⟩
    simp only [hΦtr, hΨtr, hΦ]
  have h3 := hSN
  have h4 : ∑ x ∈ SL, hL x = ∑ t ∈ SL.image Φtr, gg' t := by
    rw [Finset.sum_image hinjΦ]
    exact Finset.sum_congr rfl (fun x hx => hval x hx)
  have h5 : ∑ t ∈ SL.image Φtr, gg' t ≤ ∑ t ∈ SR.image Ψtr, gg' t :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hnonneg t)
  have h6 : ∑ t ∈ SR.image Ψtr, gg' t = ∑ y ∈ SR, gg y := by
    rw [Finset.sum_image hinjΨ]
  calc bilinear c X Y Z D a
      ≤ ∑ d ∈ moduli D a, (d.totient : ℝ)⁻¹ *
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ ≠ 1),
            ‖∑ n ∈ nRange X, c n * χ n‖ * ‖∑ p ∈ pRange Y Z, χ p‖ := hstep
    _ = ∑ x ∈ SL, hL x := h3
    _ = ∑ t ∈ SL.image Φtr, gg' t := h4
    _ ≤ ∑ t ∈ SR.image Ψtr, gg' t := h5
    _ = ∑ r ∈ conductors D a, conductorTerm c X Y Z D a r := by rw [h6, hRN]
/-- Split display 12 at the common cutoff. OPEN through primitive_reduction. -/
theorem split_reduction (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (a : ℤ)
    (hD : 1 < D) (ha : Even a) :
    bilinear c X Y Z D a ≤ smallMass c X Y Z D D₀ a + largeMass c X Y Z D D₀ a := by
  simpa only [smallMass, largeMass, not_le] using
    (primitive_reduction c X Y Z D a hD ha).trans_eq
      (sum_filter_add_sum_filter_not (conductors D a) (fun r : ℕ => (r : ℝ) ≤ D₀)
        (fun r => conductorTerm c X Y Z D a r)).symm
end
end LeanLab.BS2022GRH.Decomp148a
#print axioms LeanLab.BS2022GRH.Decomp148a.orthogonality_bound
#print axioms LeanLab.BS2022GRH.Decomp148a.primitive_reduction
#print axioms LeanLab.BS2022GRH.Decomp148a.split_reduction
