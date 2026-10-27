/-
P0083, page 488, equation 34. Explicit counting in polynomial residue classes.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Roots

namespace LeanLab.Perelli1996.Counting
open Finset Real Polynomial

/-- A periodic predicate has count error at most one period's count. -/
theorem periodic_count_error (P : ℕ → Prop) [DecidablePred P] (a L d : ℕ)
    (hd : 0 < d) (hP : Function.Periodic P d) :
    |(((Ico a (a + L)).filter P).card : ℝ) -
      (((range d).filter P).card : ℝ) / d * L| ≤ ((range d).filter P).card := by
  let ρ : ℕ := ((range d).filter P).card
  have hblock (m : ℕ) : ((Ico a (a + d * m)).filter P).card = m * ρ := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hU : Ico a (a + d * (m + 1)) =
          Ico a (a + d * m) ∪ Ico (a + d * m) (a + d * m + d) := by
        rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
        congr 1
        ring
      have hdis : Disjoint (Ico a (a + d * m)) (Ico (a + d * m) (a + d * m + d)) :=
        Finset.Ico_disjoint_Ico_consecutive _ _ _
      have hlast := Nat.filter_Ico_card_eq_of_periodic (a + d * m) d P hP
      rw [Nat.count_eq_card_filter_range] at hlast
      rw [hU, Finset.filter_union, Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter hdis), ih, hlast]
      dsimp [ρ]
      ring
  let m := L / d
  have hLlo : d * m ≤ L := Nat.mul_div_le L d
  have hLhi : L ≤ d * (m + 1) := by
    have hmod := Nat.mod_lt L hd
    have heq := Nat.mod_add_div L d
    dsimp [m]
    rw [Nat.mul_succ]
    omega
  have hcLo : m * ρ ≤ ((Ico a (a + L)).filter P).card := by
    rw [← hblock]
    apply Finset.card_le_card
    exact Finset.filter_subset_filter _ (Finset.Ico_subset_Ico le_rfl (by omega))
  have hcHi : ((Ico a (a + L)).filter P).card ≤ (m + 1) * ρ := by
    rw [← hblock]
    apply Finset.card_le_card
    exact Finset.filter_subset_filter _ (Finset.Ico_subset_Ico le_rfl (by omega))
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmLo : (m : ℝ) ≤ (L : ℝ) / d := by
    apply (le_div_iff₀ hdR).2
    exact_mod_cast (show m * d ≤ L by simpa [Nat.mul_comm] using hLlo)
  have hmHi : (L : ℝ) / d ≤ (m : ℝ) + 1 := by
    apply (div_le_iff₀ hdR).2
    exact_mod_cast (show L ≤ (m + 1) * d by simpa [Nat.mul_comm] using hLhi)
  have hlo := mul_le_mul_of_nonneg_left hmLo (Nat.cast_nonneg ρ)
  have hhi := mul_le_mul_of_nonneg_left hmHi (Nat.cast_nonneg ρ)
  have hcLoR : (m : ℝ) * ρ ≤ ((Ico a (a + L)).filter P).card := by exact_mod_cast hcLo
  have hcHiR : (((Ico a (a + L)).filter P).card : ℝ) ≤ ((m : ℝ) + 1) * ρ := by exact_mod_cast hcHi
  change |(((Ico a (a + L)).filter P).card : ℝ) - (ρ : ℝ) / d * L| ≤ ρ
  rw [show (ρ : ℝ) / d * L = (ρ : ℝ) * ((L : ℝ) / d) by ring, abs_le]
  constructor <;> nlinarith

/-- Polynomial root predicates are periodic modulo every d. -/
theorem root_periodic (F : ℤ[X]) (d : ℕ) :
    Function.Periodic (fun n : ℕ => (d : ℤ) ∣ Fv F n) d := by
  intro n
  apply propext
  have hdvd : (d : ℤ) ∣ Fv F (n + d) - Fv F n := by
    have hpoly := Polynomial.sub_dvd_eval_sub ((n + d : ℕ) : ℤ) (n : ℤ) F
    have hsub : (d : ℤ) ∣ ((n + d : ℕ) : ℤ) - (n : ℤ) := by
      refine ⟨1, ?_⟩
      push_cast
      ring
    exact dvd_trans hsub hpoly
  constructor
  · intro h
    have hdiff := dvd_sub h hdvd
    simpa using hdiff
  · intro h
    have hadd := dvd_add hdvd h
    simpa using hadd

/-- Integer interval version of equation 34 with an explicit error of rho. -/
theorem root_count_error (F : ℤ[X]) (a L d : ℕ) (hd : 0 < d) :
    |(((Ico a (a + L)).filter (fun n => (d : ℤ) ∣ Fv F n)).card : ℝ) -
      ((Roots.rootResidues F d).card : ℝ) / d * L| ≤ (Roots.rootResidues F d).card := by
  classical
  exact periodic_count_error _ a L d hd (root_periodic F d)

/-- Polynomial roots in a real interval, as used in equation 34. -/
noncomputable def rootWindow (F : ℤ[X]) (d : ℕ) (x H : ℝ) : Finset ℕ :=
  (Icc ⌈x⌉₊ ⌊x + H⌋₊).filter (fun n => (d : ℤ) ∣ Fv F n)

/-- Equation 34 for real interval endpoints, with error at most twice rho. -/
theorem root_window_error (F : ℤ[X]) (d : ℕ) (hd : 0 < d) {x H : ℝ}
    (hx : 0 ≤ x) (hH : 0 ≤ H) :
    |((rootWindow F d x H).card : ℝ) - ((Roots.rootResidues F d).card : ℝ) / d * H| ≤
      2 * (Roots.rootResidues F d).card := by
  classical
  let a := ⌈x⌉₊
  let b := ⌊x + H⌋₊
  have hab : a ≤ b + 1 := by
    have h1 : (a : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
    have h2 : x + H < (b : ℝ) + 1 := Nat.lt_floor_add_one _
    have hlt : (a : ℝ) < (b : ℝ) + 2 := by linarith
    have hnat : a < b + 2 := by exact_mod_cast hlt
    omega
  let L := b + 1 - a
  have hwin : Icc a b = Ico a (a + L) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    dsimp [L]
    omega
  have hLc : (L : ℝ) = (b : ℝ) + 1 - a := by
    dsimp [L]
    rw [Nat.cast_sub hab]
    push_cast
    ring
  have hLH : |(L : ℝ) - H| ≤ 1 := by
    have h1 : (a : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
    have h2 : x + H < (b : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : x ≤ (a : ℝ) := Nat.le_ceil x
    have h4 : (b : ℝ) ≤ x + H := Nat.floor_le (by linarith)
    rw [abs_le, hLc]
    constructor <;> linarith
  let ρ : ℝ := (Roots.rootResidues F d).card
  have hρ : 0 ≤ ρ := Nat.cast_nonneg _
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hratio : ρ / d ≤ ρ := by
    apply (div_le_iff₀ hdR).2
    nlinarith
  have herr : |ρ / d * ((L : ℝ) - H)| ≤ ρ := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hρ hdR.le)]
    calc ρ / d * |(L : ℝ) - H| ≤ ρ / d * 1 :=
          mul_le_mul_of_nonneg_left hLH (div_nonneg hρ hdR.le)
      _ ≤ ρ := by simpa using hratio
  have hc := root_count_error F a L d hd
  change |(((Ico a (a + L)).filter (fun n => (d : ℤ) ∣ Fv F n)).card : ℝ) -
    ρ / d * L| ≤ ρ at hc
  unfold rootWindow
  change |(((Icc a b).filter (fun n => (d : ℤ) ∣ Fv F n)).card : ℝ) - ρ / d * H| ≤ 2 * ρ
  rw [hwin]
  calc |(((Ico a (a + L)).filter (fun n => (d : ℤ) ∣ Fv F n)).card : ℝ) - ρ / d * H|
      = |((((Ico a (a + L)).filter (fun n => (d : ℤ) ∣ Fv F n)).card : ℝ) - ρ / d * L) +
          ρ / d * ((L : ℝ) - H)| := by congr 1; ring
    _ ≤ |(((Ico a (a + L)).filter (fun n => (d : ℤ) ∣ Fv F n)).card : ℝ) - ρ / d * L| +
        |ρ / d * ((L : ℝ) - H)| := abs_add_le _ _
    _ ≤ 2 * ρ := by linarith

end LeanLab.Perelli1996.Counting
