/-
Pin2 = J. Pintz, arXiv 1804.09084, Section 2, displays (2.15), (2.19) to (2.21): the main term
of Theorem A is large when the starred sum (2.21) is below `1 - 2ε`.
Unit U-1369, PC run 20261021T0604Z-1697, track T2, paper P0054.

Source note: the brief names P0054 Theorem 1, display (2.20), with the generalized singular
series (2.5) to (2.7). P0054 has no arXiv copy, and the permitted source Pin2 numbers these
differently: Pin2 (2.20) is the Beta bound `|B(ϱᵢ, ϱⱼ)| ≤ 1 + O(1/log X)`, Pin2 Theorem 1 is
(1.9), `E(X) < X^{0.72}`, and the generalized singular series is given in Pin2 only through
(2.11) to (2.13), its explicit form being the Main Lemma of Pin1. So this file states Pin2
(2.20), (2.12) with (2.13) as a predicate, and (2.21), and derives `RemainingMain` from them.

* `Hyp_220`: (2.19), (2.20), `‖Γ(ϱᵢ)Γ(ϱⱼ)/Γ(ϱᵢ+ϱⱼ)‖ ≤ bB`, Pin2 has `bB = 1 + O(1/log X)`.
* `Hyp_212`: (2.12), `‖𝔖(χᵢ,χⱼ,m)‖ ≤ η` unless the pair satisfies (2.13), the predicate `star`.
* `Hyp_221`: (2.21), the starred sum of `Y^{-δᵢ-δⱼ}` over pairs other than `(1,1)` is at
  most `1 - 2ε`, `ϱ = 1 - δ + iγ`.
* `remainingMain_of_221`: PROVED from these hypotheses: `RemainingMain` at EVERY level ϑ and
  every `C`, with `δ = ε C₀/4`; this is Pin2's sentence "(2.15) will follow if we can show
  (2.21)", made explicit with the factor `2^{2 dmax}` from `m ≥ Y/2`.
* `exponent_of_221`: CONDITIONAL ON `Pin2Inputs221 (2/5) ε`: `E(X) < X^α` for `α > 3/5 + 3ε`.
  (2.21) at every large scale is NOT known; Pin2 says it "can be estimated directly by density
  theorems and the Deuring-Heilbronn phenomenon" only in part, and handles the rest by the class
  split after (2.22). No improvement on 0.72 is claimed or obtained.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-21.
-/
import Mathlib
import LeanLab.Pintz2021.TheoremAU1357

namespace LeanLab.Pintz2021.Theorem1U1369

open Real Finset Filter Topology MeasureTheory LeanLab.ExceptionalSet
open LeanLab.Pintz2021.Applications LeanLab.Pintz2021.MinorArcs LeanLab.Pintz2021.Reduction3
open LeanLab.Pintz2021.Theorem3Prime LeanLab.Pintz2021.ExponentU1341
open LeanLab.Pintz2021.TheoremAU1357

attribute [local instance] Classical.propDecidable

/-- `δᵢ = 1 - Re ϱᵢ`, from `ϱ = 1 - δ + iγ` in Pin2. -/
noncomputable def δz {K : ℕ} (D : ZeroData K) (i : Fin K) : ℝ := 1 - (D.ρ i).re

/-- (2.7), (2.8), (2.11): the index `i0` is the pole `ϱ₀ = 1`, `A(ϱ₀) = 1`, with
`𝔖(χ₀, χ₀, m) = 𝔖(m)` for even `m`. -/
def Norm0 {K : ℕ} (D : ZeroData K) (i0 : Fin K) : Prop :=
  D.A i0 = 1 ∧ D.ρ i0 = 1 ∧ ∀ m, Even m → D.Sg i0 i0 m = Sing m

/-- (2.19), (2.20): `‖Γ(ϱᵢ)Γ(ϱⱼ)/Γ(ϱᵢ+ϱⱼ)‖ = ‖B(ϱᵢ, ϱⱼ)‖ ≤ bB`. -/
def Hyp_220 {K : ℕ} (D : ZeroData K) (bB : ℝ) : Prop :=
  ∀ i j, ‖Complex.Gamma (D.ρ i) * Complex.Gamma (D.ρ j) / Complex.Gamma (D.ρ i + D.ρ j)‖ ≤ bB

/-- (2.12): `‖𝔖(χᵢ, χⱼ, m)‖ ≤ η` unless `(i, j, m)` satisfies (2.13), the predicate `star`. -/
def Hyp_212 {K : ℕ} (D : ZeroData K) (star : Fin K → Fin K → ℕ → Prop) (η : ℝ) : Prop :=
  ∀ i j m, Even m → ¬ star i j m → ‖D.Sg i j m‖ ≤ η

/-- (2.21) on the block `(Y/2, Y]`: `∑*_{(i,j) ≠ (0,0)} Y^{-δᵢ-δⱼ} ≤ 1 - 2ε`. -/
def Hyp_221 {K : ℕ} (D : ZeroData K) (i0 : Fin K) (star : Fin K → Fin K → ℕ → Prop)
    (Y : ℕ) (ε : ℝ) : Prop :=
  ∀ m ∈ Ioc (Y / 2) Y, Even m →
    ∑ p ∈ ((univ ×ˢ univ).erase (i0, i0)).filter (fun p => star p.1 p.2 m),
      (Y : ℝ) ^ (-(δz D p.1 + δz D p.2)) ≤ 1 - 2 * ε

/-- HELPER: the `(0,0)` term of (2.10) is `𝔖(m) m`. -/
theorem term00 {K : ℕ} (D : ZeroData K) (i0 : Fin K) (h0 : Norm0 D i0) {m : ℕ}
    (hm : Even m) :
    ((D.A i0 : ℂ) * D.A i0) * D.Sg i0 i0 m *
      (Complex.Gamma (D.ρ i0) * Complex.Gamma (D.ρ i0) / Complex.Gamma (D.ρ i0 + D.ρ i0)) *
      (m : ℂ) ^ (D.ρ i0 + D.ρ i0 - 1) = ((Sing m * m : ℝ) : ℂ) := by
  obtain ⟨hA, hρ, hS⟩ := h0
  have h2 : Complex.Gamma (1 + 1) = 1 := by
    rw [Complex.Gamma_add_one 1 one_ne_zero, Complex.Gamma_one, one_mul]
  rw [hA, hρ, hS m hm, h2, Complex.Gamma_one, show (1 : ℂ) + 1 - 1 = 1 by ring,
    Complex.cpow_one]
  push_cast; ring

/-- HELPER: the bound on one term other than `(0,0)`. -/
theorem term_le {K : ℕ} (D : ZeroData K) {P bB η dmax : ℝ} (hsh : ZeroShape D P)
    (hB : Hyp_220 D bB) (hbB : 0 ≤ bB) (h211 : Hyp_211 D)
    (star : Fin K → Fin K → ℕ → Prop) (h212 : Hyp_212 D star η)
    (hδ : ∀ i, 0 ≤ δz D i ∧ δz D i ≤ dmax) {Y m : ℕ} (hm : m ∈ Ioc (Y / 2) Y) (he : Even m)
    (i j : Fin K) :
    ‖((D.A i : ℂ) * D.A j) * D.Sg i j m *
      (Complex.Gamma (D.ρ i) * Complex.Gamma (D.ρ j) / Complex.Gamma (D.ρ i + D.ρ j)) *
      (m : ℂ) ^ (D.ρ i + D.ρ j - 1)‖ ≤
      m * bB * (if star i j m then
        Sing m * (2 : ℝ) ^ (2 * dmax) * (Y : ℝ) ^ (-(δz D i + δz D j)) else η) := by
  obtain ⟨hm1, hm2⟩ := mem_Ioc.mp hm
  have hm0 : 0 < m := by omega
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm0
  have hYm : (m : ℝ) ≤ Y := by exact_mod_cast hm2
  have hY2 : (Y : ℝ) / 2 ≤ m := by
    have : Y ≤ 2 * m := by omega
    have : (Y : ℝ) ≤ 2 * m := by exact_mod_cast this
    linarith
  have hYpos : (0 : ℝ) < Y := by linarith
  have hA : ∀ k, ‖(D.A k : ℂ)‖ = 1 := fun k => by
    rcases hsh.1 k with h | h <;> simp [h]
  set d := δz D i + δz D j with hd
  have hd0 : 0 ≤ d := by linarith [(hδ i).1, (hδ j).1]
  have hd1 : d ≤ 2 * dmax := by linarith [(hδ i).2, (hδ j).2]
  have hpow : ‖(m : ℂ) ^ (D.ρ i + D.ρ j - 1)‖ = m * (m : ℝ) ^ (-d) := by
    rw [Complex.norm_natCast_cpow_of_pos hm0]
    have : (D.ρ i + D.ρ j - 1).re = 1 + -d := by
      simp only [hd, δz, Complex.sub_re, Complex.add_re, Complex.one_re]; ring
    rw [this, rpow_add (by linarith), rpow_one]
  have hmd : (m : ℝ) ^ (-d) ≤ 1 := rpow_le_one_of_one_le_of_nonpos hmr (by linarith)
  have hmd2 : (m : ℝ) ^ (-d) ≤ (2 : ℝ) ^ (2 * dmax) * (Y : ℝ) ^ (-d) := by
    have h1 : (m : ℝ) ^ (-d) ≤ ((Y : ℝ) / 2) ^ (-d) :=
      rpow_le_rpow_of_nonpos (by positivity) hY2 (by linarith)
    have h2 : ((Y : ℝ) / 2) ^ (-d) = (2 : ℝ) ^ d * (Y : ℝ) ^ (-d) := by
      rw [div_rpow hYpos.le (by norm_num), rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
    have h3 : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ (2 * dmax) := rpow_le_rpow_of_exponent_le (by norm_num) hd1
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hA, hA, hpow, one_mul, one_mul]
  have hG := hB i j
  have hSing0 : 0 ≤ Sing m := le_trans (by linarith [C0_pos]) (two_C0_le_Sing' m)
  have hm0r : (0 : ℝ) ≤ m := by linarith
  split_ifs with hs
  · have hS := h211 i j m he
    calc ‖D.Sg i j m‖ * ‖Complex.Gamma (D.ρ i) * Complex.Gamma (D.ρ j) /
          Complex.Gamma (D.ρ i + D.ρ j)‖ * (m * (m : ℝ) ^ (-d))
        ≤ Sing m * bB * (m * ((2 : ℝ) ^ (2 * dmax) * (Y : ℝ) ^ (-d))) := by
          gcongr
      _ = _ := by ring
  · have hS := h212 i j m he hs
    have hη : 0 ≤ η := (norm_nonneg _).trans hS
    calc ‖D.Sg i j m‖ * ‖Complex.Gamma (D.ρ i) * Complex.Gamma (D.ρ j) /
          Complex.Gamma (D.ρ i + D.ρ j)‖ * (m * (m : ℝ) ^ (-d))
        ≤ η * bB * (m * 1) := by gcongr
      _ = _ := by ring

/-- PROVED from (2.7), (2.8), (2.11), (2.12), (2.19), (2.20), (2.21) and the margins
`bB 2^{2 dmax} (1 - 2ε) ≤ 1 - ε`, `bB η K² ≤ ε C₀`: `RemainingMain D Y C ϑ (ε C₀/4)` for
every `ϑ` and `C`. The class condition `q(ℛ') ≤ Y^ϑ` is not used. -/
theorem remainingMain_of_221 {K : ℕ} (D : ZeroData K) (i0 : Fin K) {P bB η dmax ε : ℝ}
    (hsh : ZeroShape D P) (h0 : Norm0 D i0) (hB : Hyp_220 D bB) (hbB : 0 ≤ bB)
    (h211 : Hyp_211 D) (star : Fin K → Fin K → ℕ → Prop) (h212 : Hyp_212 D star η)
    (hδ : ∀ i, 0 ≤ δz D i ∧ δz D i ≤ dmax) {Y : ℕ} (h221 : Hyp_221 D i0 star Y ε)
    (hm1 : bB * (2 : ℝ) ^ (2 * dmax) * (1 - 2 * ε) ≤ 1 - ε)
    (hm2 : bB * η * (K : ℝ) ^ 2 ≤ ε * C0) (hε : 0 ≤ ε) (hη : 0 ≤ η) (C : ℕ) (ϑ : ℝ) :
    RemainingMain D Y C ϑ (ε * C0 / 4) := by
  intro m hm he _
  obtain ⟨hmY1, hmY2⟩ := mem_Ioc.mp hm
  have hY2 : (Y : ℝ) / 2 ≤ m := by
    have : Y ≤ 2 * m := by omega
    have : (Y : ℝ) ≤ 2 * m := by exact_mod_cast this
    linarith
  have hm0r : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set f : Fin K × Fin K → ℂ := fun p => ((D.A p.1 : ℂ) * D.A p.2) * D.Sg p.1 p.2 m *
    (Complex.Gamma (D.ρ p.1) * Complex.Gamma (D.ρ p.2) / Complex.Gamma (D.ρ p.1 + D.ρ p.2)) *
    (m : ℂ) ^ (D.ρ p.1 + D.ρ p.2 - 1) with hf
  have hmain : mainTerm D m = f (i0, i0) + ∑ p ∈ (univ ×ˢ univ).erase (i0, i0), f p := by
    rw [add_sum_erase _ _ (mem_product.mpr ⟨mem_univ _, mem_univ _⟩)]
    unfold mainTerm
    rw [sum_product]
  set g : Fin K × Fin K → ℝ := fun p => if star p.1 p.2 m then
    Sing m * (2 : ℝ) ^ (2 * dmax) * (Y : ℝ) ^ (-(δz D p.1 + δz D p.2)) else η with hg
  have hterm : ∀ p, ‖f p‖ ≤ m * bB * g p := fun p =>
    term_le D hsh hB hbB h211 star h212 hδ hm he p.1 p.2
  set s := (univ ×ˢ univ : Finset (Fin K × Fin K)).erase (i0, i0)
  have hgsum : ∑ p ∈ s, g p ≤ Sing m * (2 : ℝ) ^ (2 * dmax) * (1 - 2 * ε) + η * (K : ℝ) ^ 2 := by
    rw [hg, sum_ite, ← mul_sum]
    have h1 := h221 m hm he
    have hSing0 : 0 ≤ Sing m := le_trans (by linarith [C0_pos]) (two_C0_le_Sing' m)
    have hA : Sing m * (2 : ℝ) ^ (2 * dmax) *
        ∑ x ∈ s.filter (fun p => star p.1 p.2 m), (Y : ℝ) ^ (-(δz D x.1 + δz D x.2)) ≤
        Sing m * (2 : ℝ) ^ (2 * dmax) * (1 - 2 * ε) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have hB2 : ∑ _x ∈ s.filter (fun p => ¬ star p.1 p.2 m), η ≤ η * (K : ℝ) ^ 2 := by
      rw [sum_const, nsmul_eq_mul]
      have hc : ((s.filter (fun p => ¬ star p.1 p.2 m)).card : ℝ) ≤ (K : ℝ) ^ 2 := by
        have : (s.filter (fun p => ¬ star p.1 p.2 m)).card ≤ K ^ 2 := by
          calc _ ≤ s.card := card_filter_le _ _
            _ ≤ (univ ×ˢ univ : Finset (Fin K × Fin K)).card := card_erase_le
            _ = K ^ 2 := by simp [card_product, sq]
        exact_mod_cast this
      nlinarith
    linarith
  have hrest : -(∑ p ∈ s, ‖f p‖) ≤ (∑ p ∈ s, f p).re := by
    have := Complex.abs_re_le_norm (∑ p ∈ s, f p)
    have := norm_sum_le s f
    linarith [(abs_le.mp ‹|(∑ p ∈ s, f p).re| ≤ _›).1]
  have hsumf : ∑ p ∈ s, ‖f p‖ ≤ m * bB * (Sing m * (2 : ℝ) ^ (2 * dmax) * (1 - 2 * ε) +
      η * (K : ℝ) ^ 2) := by
    calc ∑ p ∈ s, ‖f p‖ ≤ ∑ p ∈ s, m * bB * g p := sum_le_sum fun p _ => hterm p
      _ = m * bB * ∑ p ∈ s, g p := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hgsum (by positivity)
  have h00 : (f (i0, i0)).re = Sing m * m := by
    have := term00 D i0 h0 he
    simp only [hf]
    rw [this, Complex.ofReal_re]
  rw [hmain, Complex.add_re, h00]
  have hSing := two_C0_le_Sing' m
  have hC0 := C0_pos
  have e1 : m * bB * (Sing m * (2 : ℝ) ^ (2 * dmax) * (1 - 2 * ε) + η * (K : ℝ) ^ 2) =
      m * Sing m * (bB * (2 : ℝ) ^ (2 * dmax) * (1 - 2 * ε)) + m * (bB * η * (K : ℝ) ^ 2) := by
    ring
  have hSing0 : 0 ≤ Sing m := by linarith
  have k1 : m * Sing m * (bB * (2 : ℝ) ^ (2 * dmax) * (1 - 2 * ε)) ≤ m * Sing m * (1 - ε) :=
    mul_le_mul_of_nonneg_left hm1 (by positivity)
  have k2 : m * (bB * η * (K : ℝ) ^ 2) ≤ m * (ε * C0) := mul_le_mul_of_nonneg_left hm2 hm0r
  have k3 : m * (ε * C0) ≤ m * Sing m * ε - m * (ε * C0) := by
    have := mul_le_mul_of_nonneg_left hSing (mul_nonneg hm0r hε)
    linarith
  have k4 : ε * C0 * Y / 2 ≤ m * (ε * C0) := by
    have := mul_le_mul_of_nonneg_right hY2 (mul_nonneg hε hC0.le)
    linarith
  have k5 : m * Sing m * (1 - ε) = Sing m * m - m * Sing m * ε := by ring
  linarith

/-- The Pin2 inputs with `RemainingMain` replaced by (2.12), (2.20), (2.21) and the margins:
Lemma 1 at `P = Y^ϑ`, Theorem A (2.10) with (2.11) and (2.14) `K ≤ Kmax`. -/
def Pin2Inputs221 (ϑ ε : ℝ) : Prop :=
  ∃ (A c H T Cerr bB η dmax : ℝ) (C Kmax Y0 : ℕ), 0 ≤ A ∧ 0 ≤ Cerr ∧ 0 < C ∧ 0 ≤ bB ∧ 0 ≤ η ∧
    Cerr * (Real.exp (-(c * H)) + 1 / Real.sqrt T) ≤ ε * C0 / 8 ∧
    bB * (2 : ℝ) ^ (2 * dmax) * (1 - 2 * ε) ≤ 1 - ε ∧ bB * η * (Kmax : ℝ) ^ 2 ≤ ε * C0 ∧
    ∀ Y : ℕ, Y0 < Y → ∃ (X1 : ℝ) (mi : Set ℝ) (K : ℕ) (D : ZeroData K) (P : ℝ) (i0 : Fin K)
      (star : Fin K → Fin K → ℕ → Prop),
      K ≤ Kmax ∧ MeasurableSet mi ∧ Lemma1On A X1 Y ((Y : ℝ) ^ ϑ) mi ∧
      (Y : ℝ) ^ (ϑ - ε) < P ∧ P < (Y : ℝ) ^ ϑ ∧ ZeroShape D P ∧ Norm0 D i0 ∧
      TheoremA_210 (R1 (S X1 Y) mi) Y ε c H T Cerr D ∧ Hyp_211 D ∧ Hyp_220 D bB ∧
      Hyp_212 D star η ∧ (∀ i, 0 ≤ δz D i ∧ δz D i ≤ dmax) ∧ Hyp_221 D i0 star Y ε

/-- PROVED: `Pin2Inputs221 ϑ ε` gives `Pin2Inputs ϑ ε`, for `ε > 0`. -/
theorem pin2Inputs_of_221 {ϑ ε : ℝ} (hε : 0 < ε) (h : Pin2Inputs221 ϑ ε) : Pin2Inputs ϑ ε := by
  obtain ⟨A, c, H, T, Cerr, bB, η, dmax, C, Kmax, Y0, hA, hCerr, hC, hbB, hη, hHT, hm1, hm2, hin⟩ := h
  refine ⟨A, ε * C0 / 4, c, H, T, Cerr, C, Kmax, Y0, hA, by have := C0_pos; positivity, hCerr,
    hC, by linarith, fun Y hY => ?_⟩
  obtain ⟨X1, mi, K, D, P, i0, star, hK, hmi, hL1, hP1, hP2, hsh, hn0, hTA, h211, h220, h212,
    hδ, h221⟩ := hin Y hY
  have hKr : (K : ℝ) ^ 2 ≤ (Kmax : ℝ) ^ 2 := by
    have : (K : ℝ) ≤ Kmax := by exact_mod_cast hK
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  have hm2' : bB * η * (K : ℝ) ^ 2 ≤ ε * C0 :=
    le_trans (mul_le_mul_of_nonneg_left hKr (mul_nonneg hbB hη)) hm2
  exact ⟨X1, mi, K, D, P, hK, hmi, hL1, hP1, hP2, hsh, hTA, h211,
    remainingMain_of_221 D i0 hsh hn0 h220 hbB h211 star h212 hδ h221 hm1 hm2' hε.le hη C ϑ⟩

/-- CONDITIONAL ON `Pin2Inputs221 (2/5) ε`: `E(X) < X^α` for large `X` when `3/5 + 3ε < α`;
in particular at `α = 0.72` once `ε < 0.04`. This is the ceiling T-1341-2 of the chain, and it
rests on (2.21) at every large scale, which is NOT known. -/
theorem exponent_of_221 {ε α : ℝ} (hε : 0 < ε) (hα : 3 / 5 + 3 * ε < α)
    (h : Pin2Inputs221 (2 / 5) ε) : EventuallyBelow α :=
  exponent_of_pin2 hε le_rfl (by linarith) (pin2Inputs_of_221 hε h)

/-- Numerics: the conditional exponent `3/5 + 3ε` is below `0.72` exactly when `ε < 0.04`, and
the level `ϑ = 2/5` exceeds `0.28 + 3ε` exactly when `ε < 0.04`. -/
theorem numerics_221 {ε : ℝ} : (3 / 5 + 3 * ε < 0.72 ↔ ε < 0.04) ∧
    ((0.28 : ℝ) + 3 * ε < 2 / 5 ↔ ε < 0.04) := by
  constructor <;> constructor <;> intro h <;> norm_num at h ⊢ <;> linarith

/-! ### Vacuity tests -/

/-- The toy data with `𝔖(χ₀, χ₀, m) = 𝔖(m)`: one index, the pole `ϱ = 1`, `A = 1`. -/
noncomputable def toy0 : ZeroData 1 where
  A := fun _ => 1
  ρ := fun _ => 1
  r := fun _ => 1
  Sg := fun _ _ m => ((Sing m : ℝ) : ℂ)

/-- Vacuity test: with the toy data `toy0`, one index, the pole, no starred pair,
the hypotheses (2.7), (2.8), (2.11), (2.12), (2.20), (2.21) hold together with `bB = 1`,
`η = 0`, `dmax = 0`, for every `Y` and every `ε ≤ 1/2`. -/
theorem hyps221_satisfiable (Y : ℕ) {ε : ℝ} (hε : ε ≤ 1 / 2) :
    ZeroShape toy0 1 ∧ Norm0 toy0 0 ∧ Hyp_220 toy0 1 ∧ Hyp_211 toy0 ∧
    Hyp_212 toy0 (fun _ _ _ => True) 0 ∧ (∀ i, 0 ≤ δz toy0 i ∧ δz toy0 i ≤ 0) ∧
    Hyp_221 toy0 0 (fun _ _ _ => True) Y ε := by
  have h2 : Complex.Gamma (1 + 1) = 1 := by
    rw [Complex.Gamma_add_one 1 one_ne_zero, Complex.Gamma_one, one_mul]
  refine ⟨⟨fun _ => Or.inl rfl, fun _ => ⟨le_rfl, by simp [toy0]⟩⟩, ⟨rfl, rfl, fun m _ => rfl⟩,
    fun i j => ?_, fun i j m _ => ?_, fun i j m _ h => (h trivial).elim, fun i => ?_,
    fun m _ _ => ?_⟩
  · simp [toy0, Complex.Gamma_one, h2]
  · simp only [toy0, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_of_nonneg (le_trans (by linarith [C0_pos]) (two_C0_le_Sing' m))).le
  · simp [δz, toy0]
  · have : ((univ ×ˢ univ : Finset (Fin 1 × Fin 1)).erase (0, 0)) = ∅ := by decide
    rw [this, filter_empty, sum_empty]; linarith

end LeanLab.Pintz2021.Theorem1U1369

#print axioms LeanLab.Pintz2021.Theorem1U1369.term00
#print axioms LeanLab.Pintz2021.Theorem1U1369.term_le
#print axioms LeanLab.Pintz2021.Theorem1U1369.remainingMain_of_221
#print axioms LeanLab.Pintz2021.Theorem1U1369.pin2Inputs_of_221
#print axioms LeanLab.Pintz2021.Theorem1U1369.exponent_of_221
#print axioms LeanLab.Pintz2021.Theorem1U1369.numerics_221
#print axioms LeanLab.Pintz2021.Theorem1U1369.hyps221_satisfiable
