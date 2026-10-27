/-
P0080 Hathi 2021, arXiv 2109.13174v3, Section 3, page 9: elementary facts on `ρ(d)`, the order of
2 modulo an odd `d`.
* (3.2), second half: `2^{ρ(d)} ≥ d + 1`, that is `ρ(d) ≥ log(d + 1)/log 2`.
* (3.3) and (3.4): `q₁ ∣ q` gives `ρ(q₁) ∣ ρ(q)`, so `ρ(q₁) ≤ ρ(q)`.
Unit U-6159, CLOUD 20261020T0717Z-cloud37. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN. KNOWN mathematics.
-/
import Mathlib

namespace LeanLab.Hathi2021.Rho

/-- `ρ(d)`, the order of 2 modulo `d`. -/
noncomputable def rho (d : ℕ) : ℕ := orderOf (2 : ZMod d)

lemma isOfFinOrder_two {d : ℕ} (hd : Odd d) : IsOfFinOrder (2 : ZMod d) := by
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd
  haveI : NeZero d := ⟨hd0⟩
  have hc : Nat.Coprime 2 d := (Nat.coprime_two_left).mpr hd
  have h : ((ZMod.unitOfCoprime 2 hc : (ZMod d)ˣ) : ZMod d) = 2 := by
    simp [ZMod.unitOfCoprime]
  rw [← h]
  exact Units.isOfFinOrder_val.mpr (isOfFinOrder_of_finite _)

lemma rho_pos {d : ℕ} (hd : Odd d) : 0 < rho d := (isOfFinOrder_two hd).orderOf_pos

/-- **(3.2): `2^{ρ(d)} ≥ d + 1`** for odd `d > 1`. -/
theorem two_pow_rho_ge {d : ℕ} (hd : Odd d) (hd1 : 1 < d) : d + 1 ≤ 2 ^ rho d := by
  have hp : (2 : ZMod d) ^ rho d = 1 := pow_orderOf_eq_one _
  have h1 : 1 ≤ 2 ^ rho d := Nat.one_le_two_pow
  have hcast : ((2 ^ rho d - 1 : ℕ) : ZMod d) = 0 := by
    rw [Nat.cast_sub h1]; push_cast; rw [hp, sub_self]
  have hdvd : d ∣ 2 ^ rho d - 1 := (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have hgt : 2 ≤ 2 ^ rho d := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ rho d := Nat.pow_le_pow_right (by norm_num) (rho_pos hd)
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

/-- **(3.3): `q₁ ∣ q` gives `ρ(q₁) ∣ ρ(q)`.** -/
theorem rho_dvd {q₁ q : ℕ} (h : q₁ ∣ q) : rho q₁ ∣ rho q := by
  unfold rho
  have := orderOf_map_dvd (ZMod.castHom h (ZMod q₁)).toMonoidHom (2 : ZMod q)
  have h2 : (ZMod.castHom h (ZMod q₁)).toMonoidHom (2 : ZMod q) = 2 := by
    show (ZMod.castHom h (ZMod q₁)) (2 : ZMod q) = 2
    exact map_ofNat _ 2
  rwa [h2] at this

/-- **(3.4), the `ρ` half: `q₁ ∣ q` gives `ρ(q₁) ≤ ρ(q)`** for odd `q`. -/
theorem rho_le {q₁ q : ℕ} (h : q₁ ∣ q) (hq : Odd q) : rho q₁ ≤ rho q :=
  Nat.le_of_dvd (rho_pos hq) (rho_dvd h)

/-- Vacuity test: `ρ(7) = 3`, `2³ = 8 = 7 + 1`. -/
example : 7 + 1 ≤ 2 ^ rho 7 := two_pow_rho_ge (by decide) (by norm_num)

end LeanLab.Hathi2021.Rho
