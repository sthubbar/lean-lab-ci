/-
P0086 Basak, Bhat, Dong, Zaharescu 2024, arXiv 2409.08968 v1, display (7.16).
`Euler716` of MajorArcs.lean PROVED unconditionally, as `euler716`.

Plain math. For `(v, q_0) = 1`, `h(v) = μ(v) c_v(m) / φ(v)³` with the Ramanujan sum
`c_v(m) = Σ_{1 ≤ a ≤ v, (a,v)=1} e(-am/v)`, else `h(v) = 0`. Then `h` is multiplicative:
`c_{vw} = c_v c_w` for coprime `v, w` by the bijection `(a, b) ↦ a w + b v mod vw`
(injective by cancelling units, surjective by counting, `φ(vw) = φ(v) φ(w)`).
At a prime `p`: `c_p(m) = p - 1` if `p | m`, `-1` otherwise, by the geometric sum of a
nontrivial `p`-th root of unity. Hence `h(p) = -1/(p-1)²` for `p | m`, `p ∤ q_0`,
`h(p) = 1/(p-1)³` for `p ∤ m`, `p ∤ q_0`, `h(p) = 0` for `p | q_0`, and `h(p^e) = 0` for `e ≥ 2`.
`Σ |h(v)|` converges since its partial sums are at most `∏_p (1 + 1/(p-1)²) ≤ e²`, and the
Mathlib Euler product gives `Σ_v h(v) = ∏_{p ∤ q_0, p | m} (1 - 1/(p-1)²) ∏_{p ∤ q_0, p ∤ m}
(1 + 1/(p-1)³)`, the PDF form of (7.16). So the sum is real and, since every factor at
`p ∤ m` is at least `1`, at least the finite product over `p | m`, `p ≥ Z`.

Lemma82 is NOT proved here.

AI-written Lean code, Claude, run 20261021T0103Z-19411, unit U-1328. Checked only by the Lean
kernel. Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.SparseTernary.MajorArcs

open Finset Filter Real
open scoped Classical

noncomputable section
namespace LeanLab.SparseTernary.LocalFactors

open LeanLab.SparseTernary LeanLab.SparseTernary.Section4 LeanLab.SparseTernary.MajorArcs

/-! ### `e(x)` -/

theorem ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem ee_int (n : ℤ) : ee (n : ℝ) = 1 := by
  unfold ee; rw [Complex.exp_eq_one_iff]; exact ⟨n, by push_cast; ring⟩

theorem ee_nat_mul (n : ℕ) (x : ℝ) : ee (n * x) = ee x ^ n := by
  unfold ee; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-! ### The Ramanujan sum -/

/-- The reduced residues `1 ≤ a ≤ v`, `(a, v) = 1`. -/
def U (v : ℕ) : Finset ℕ := (Icc 1 v).filter (fun a => a.Coprime v)

/-- `c_v(m) = Σ_{a ∈ U v} e(-am/v)`. -/
def ram (v m : ℕ) : ℂ := ∑ a ∈ U v, ee (-((a : ℝ) * m / v))

theorem hv_eq (Z m v : ℕ) : hv Z m v =
    if v.Coprime (q0 Z) then (ArithmeticFunction.moebius v : ℂ) / (v.totient : ℂ) ^ 3 * ram v m
    else 0 := rfl

theorem card_U (v : ℕ) : #(U v) = v.totient := by
  have := Nat.filter_coprime_Ico_eq_totient v 1
  rw [← this]; unfold U
  congr 1
  ext a; simp only [mem_filter, mem_Icc, mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h3.symm⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h3.symm⟩

theorem U_eq_of_modEq {v a a' : ℕ} (ha : a ∈ U v) (ha' : a' ∈ U v) (h : a ≡ a' [MOD v]) :
    a = a' := by
  simp only [U, mem_filter, mem_Icc] at ha ha'
  rcases Nat.lt_or_ge v 2 with hv | hv
  · omega
  have hlt : ∀ b, 1 ≤ b → b ≤ v → b.Coprime v → b < v := by
    intro b _ hb2 hb3
    rcases Nat.lt_or_ge b v with h' | h'
    · exact h'
    · have : b = v := by omega
      subst this; rw [Nat.coprime_self] at hb3; omega
  have h1 := hlt a ha.1.1 ha.1.2 ha.2
  have h2 := hlt a' ha'.1.1 ha'.1.2 ha'.2
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h

theorem ram_one (m : ℕ) : ram 1 m = 1 := by
  unfold ram U
  have : (Icc 1 1).filter (fun a => a.Coprime 1) = {1} := by decide
  rw [this, sum_singleton]
  have := ee_int (-(m : ℤ))
  push_cast at this ⊢
  simpa using this

/-- The CRT step: `c_{vw}(m) = c_v(m) c_w(m)` for coprime `v, w ≥ 1`. -/
theorem ram_mul (v w m : ℕ) (hv : 1 ≤ v) (hw : 1 ≤ w) (hvw : v.Coprime w) :
    ram (v * w) m = ram v m * ram w m := by
  set n := v * w with hn
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- the map
  let φ : ℕ × ℕ → ℕ := fun t => (t.1 * w + t.2 * v - 1) % n + 1
  let k : ℕ × ℕ → ℕ := fun t => (t.1 * w + t.2 * v - 1) / n
  have hx1 : ∀ t ∈ U v ×ˢ U w, 1 ≤ t.1 * w + t.2 * v := by
    intro t ht
    simp only [U, mem_product, mem_filter, mem_Icc] at ht
    nlinarith
  have hφk : ∀ t ∈ U v ×ˢ U w, φ t + n * k t = t.1 * w + t.2 * v := by
    intro t ht
    have := Nat.mod_add_div (t.1 * w + t.2 * v - 1) n
    have h1 := hx1 t ht
    simp only [φ, k]; omega
  have hmodφ : ∀ t ∈ U v ×ˢ U w, φ t ≡ t.1 * w + t.2 * v [MOD n] := by
    intro t ht
    rw [← hφk t ht]; unfold Nat.ModEq; rw [Nat.add_mul_mod_self_left]
  have hcopx : ∀ t ∈ U v ×ˢ U w, (t.1 * w + t.2 * v).Coprime n := by
    intro t ht
    simp only [U, mem_product, mem_filter, mem_Icc] at ht
    rw [hn, Nat.coprime_mul_iff_right]
    constructor
    · rw [Nat.coprime_add_mul_right_left, Nat.coprime_mul_iff_left]
      exact ⟨ht.1.2, hvw.symm⟩
    · rw [add_comm, Nat.coprime_add_mul_right_left, Nat.coprime_mul_iff_left]
      exact ⟨ht.2.2, hvw⟩
  have hmem : ∀ t ∈ U v ×ˢ U w, φ t ∈ U n := by
    intro t ht
    simp only [U, mem_filter, mem_Icc]
    refine ⟨⟨by simp only [φ]; omega, ?_⟩, ?_⟩
    · have := Nat.mod_lt (t.1 * w + t.2 * v - 1) (by omega : 0 < n); simp only [φ]; omega
    · have := hcopx t ht
      rw [← hφk t ht, mul_comm n (k t), Nat.coprime_add_mul_right_left] at this
      exact this
  have hinj : ∀ t ∈ U v ×ˢ U w, ∀ t' ∈ U v ×ˢ U w, φ t = φ t' → t = t' := by
    intro t ht t' ht' he
    have hxx : t.1 * w + t.2 * v ≡ t'.1 * w + t'.2 * v [MOD n] :=
      ((hmodφ t ht).symm.trans (by rw [he])).trans (hmodφ t' ht')
    have hv' : t.1 * w + t.2 * v ≡ t'.1 * w + t'.2 * v [MOD v] :=
      Nat.ModEq.of_mul_right w (by rw [← hn]; exact hxx)
    have hw' : t.1 * w + t.2 * v ≡ t'.1 * w + t'.2 * v [MOD w] :=
      Nat.ModEq.of_mul_left v (by rw [← hn]; exact hxx)
    have ha : t.1 ≡ t'.1 [MOD v] := by
      refine Nat.ModEq.cancel_right_of_coprime (c := w) (Nat.Coprime.gcd_eq_one hvw) ?_
      unfold Nat.ModEq at hv' ⊢
      rwa [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at hv'
    have hb : t.2 ≡ t'.2 [MOD w] := by
      refine Nat.ModEq.cancel_right_of_coprime (c := v) (Nat.Coprime.gcd_eq_one hvw.symm) ?_
      unfold Nat.ModEq at hw' ⊢
      rwa [add_comm, Nat.add_mul_mod_self_right, add_comm, Nat.add_mul_mod_self_right] at hw'
    have ht1 := mem_product.mp ht
    have ht1' := mem_product.mp ht'
    exact Prod.ext (U_eq_of_modEq ht1.1 ht1'.1 ha) (U_eq_of_modEq ht1.2 ht1'.2 hb)
  have hcard : #(U n) ≤ #(U v ×ˢ U w) := by
    rw [card_product, card_U, card_U, card_U, hn, Nat.totient_mul hvw]
  have hsurj := surj_on_of_inj_on_of_card_le (fun t _ => φ t) hmem
    (fun a b ha hb h => hinj a ha b hb h) hcard
  -- the values agree
  have hval : ∀ t ∈ U v ×ˢ U w,
      ee (-((t.1 : ℝ) * m / v)) * ee (-((t.2 : ℝ) * m / w)) = ee (-((φ t : ℝ) * m / n)) := by
    intro t ht
    have e := hφk t ht
    have e' : (φ t : ℝ) = (t.1 : ℝ) * w + t.2 * v - n * k t := by
      have : ((φ t + n * k t : ℕ) : ℝ) = ((t.1 * w + t.2 * v : ℕ) : ℝ) := by rw [e]
      push_cast at this; linarith
    have hv0 : (v : ℝ) ≠ 0 := by positivity
    have hw0 : (w : ℝ) ≠ 0 := by positivity
    have hnR : (n : ℝ) = v * w := by rw [hn]; push_cast; ring
    have : -((φ t : ℝ) * m / n) = (-((t.1 : ℝ) * m / v) + -((t.2 : ℝ) * m / w)) +
        (((k t * m : ℕ) : ℤ) : ℝ) := by
      rw [e', hnR]; push_cast; field_simp; ring
    rw [this, ee_add _ (((k t * m : ℕ) : ℤ) : ℝ), ee_int, mul_one, ee_add]
  unfold ram
  rw [sum_mul_sum, ← sum_product']
  symm
  refine sum_bij (fun t _ => φ t) hmem (fun a ha b hb h => hinj a ha b hb h) ?_ hval
  intro b hb
  obtain ⟨a, ha, h⟩ := hsurj b hb
  exact ⟨a, ha, h.symm⟩

/-- `c_p(m)` at a prime. -/
theorem ram_prime (p m : ℕ) (hp : p.Prime) :
    ram p m = if p ∣ m then ((p : ℂ) - 1) else -1 := by
  have hU : U p = Ico 1 p := by
    ext a; simp only [U, mem_filter, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, lt_of_le_of_ne h2 ?_⟩
      rintro rfl; rw [Nat.coprime_self] at h3; exact hp.one_lt.ne' h3
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, h2.le⟩, ?_⟩
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hd; exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpow : ∀ a : ℕ, ee (-((a : ℝ) * m / p)) = ee (-((m : ℝ) / p)) ^ a := by
    intro a; rw [← ee_nat_mul]; congr 1; ring
  unfold ram; rw [hU]
  split_ifs with hd
  · obtain ⟨c, rfl⟩ := hd
    have : ∀ a ∈ Ico 1 p, ee (-((a : ℝ) * ((p * c : ℕ) : ℝ) / p)) = 1 := by
      intro a _
      have : -((a : ℝ) * ((p * c : ℕ) : ℝ) / p) = ((-(a * c : ℤ) : ℤ) : ℝ) := by
        push_cast; field_simp
      rw [this, ee_int]
    rw [sum_congr rfl this, sum_const, Nat.card_Ico]
    simp [Nat.cast_sub hp.one_le]
  · set ζ := ee (-((m : ℝ) / p))
    have hζp : ζ ^ p = 1 := by
      rw [← ee_nat_mul]
      have : (p : ℝ) * -((m : ℝ) / p) = ((-(m : ℤ) : ℤ) : ℝ) := by push_cast; field_simp
      rw [this, ee_int]
    have hζ1 : ζ ≠ 1 := by
      intro h
      unfold ζ ee at h
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
      have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h2 : ((-((m : ℝ) / p) : ℝ) : ℂ) = (n : ℂ) := by
        have := hn; rw [mul_comm (n : ℂ)] at this
        exact mul_left_cancel₀ hpi this
      have h3 : -((m : ℝ) / p) = (n : ℝ) := by exact_mod_cast h2
      have h4 : ((m : ℤ) : ℝ) = ((-n * p : ℤ) : ℝ) := by
        push_cast; field_simp at h3; linarith
      have h5 : (m : ℤ) = -n * p := by exact_mod_cast h4
      apply hd
      have : (p : ℤ) ∣ (m : ℤ) := ⟨-n, by rw [h5]; ring⟩
      exact_mod_cast this
    have hgeom : ∑ a ∈ range p, ζ ^ a = 0 := by
      rw [geom_sum_eq hζ1, hζp, sub_self, zero_div]
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hp.pos, pow_zero] at hgeom
    rw [sum_congr rfl (fun a _ => hpow a)]
    linear_combination hgeom

/-! ### `h` -/

theorem prime_coprime_q0 (Z p : ℕ) (hp : p.Prime) : p.Coprime (q0 Z) ↔ Z ≤ p := by
  rw [hp.coprime_iff_not_dvd]
  unfold q0
  rw [Prime.dvd_finsetProd_iff hp.prime]
  constructor
  · intro h
    by_contra hlt
    exact h ⟨p, by simp [Nat.primesBelow, hp]; omega, dvd_rfl⟩
  · rintro h ⟨q, hq, hd⟩
    have hq' := Nat.prime_of_mem_primesBelow hq
    have := (Nat.prime_dvd_prime_iff_eq hp hq').mp hd
    subst this
    have := Nat.lt_of_mem_primesBelow hq; omega

/-- The real value of `h(p)`. -/
def hp (Z m p : ℕ) : ℝ :=
  if Z ≤ p then (if p ∣ m then -1 / ((p : ℝ) - 1) ^ 2 else 1 / ((p : ℝ) - 1) ^ 3) else 0

theorem hv_prime (Z m p : ℕ) (hpp : p.Prime) : hv Z m p = (hp Z m p : ℂ) := by
  have hc := prime_coprime_q0 Z p hpp
  rw [hv_eq, ram_prime p m hpp, ArithmeticFunction.moebius_apply_prime hpp,
    Nat.totient_prime hpp]
  unfold hp
  by_cases hZ : Z ≤ p
  · rw [if_pos (hc.mpr hZ), if_pos hZ]
    split_ifs <;> push_cast [Nat.cast_sub hpp.one_le] <;> field_simp <;> ring
  · rw [if_neg (fun h => hZ (hc.mp h)), if_neg hZ]; simp

theorem hv_zero (Z m : ℕ) : hv Z m 0 = 0 := by
  rw [hv_eq]; simp

theorem hv_one (Z m : ℕ) : hv Z m 1 = 1 := by
  rw [hv_eq, ram_one]; simp

theorem hv_mul (Z m : ℕ) {v w : ℕ} (h : v.Coprime w) : hv Z m (v * w) = hv Z m v * hv Z m w := by
  rcases Nat.eq_zero_or_pos v with rfl | hv0
  · rw [Nat.coprime_zero_left] at h; subst h; simp [hv_one]
  rcases Nat.eq_zero_or_pos w with rfl | hw0
  · rw [Nat.coprime_zero_right] at h; subst h; simp [hv_one]
  rw [hv_eq, hv_eq, hv_eq]
  by_cases h1 : v.Coprime (q0 Z)
  · by_cases h2 : w.Coprime (q0 Z)
    · rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨h1, h2⟩), if_pos h1, if_pos h2, ram_mul v w m hv0 hw0 h,
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h, Nat.totient_mul h]
      push_cast; ring
    · rw [if_neg (fun hc => h2 (Nat.coprime_mul_iff_left.mp hc).2), if_neg h2, mul_zero]
  · rw [if_neg (fun hc => h1 (Nat.coprime_mul_iff_left.mp hc).1), if_neg h1, zero_mul]

theorem hv_prime_pow (Z m p e : ℕ) (hpp : p.Prime) (he : 2 ≤ e) : hv Z m (p ^ e) = 0 := by
  rw [hv_eq, ArithmeticFunction.moebius_apply_prime_pow hpp (by omega)]
  simp; omega

theorem tsum_prime_pow {f : ℕ → ℂ} {p : ℕ} (hf1 : f 1 = 1) (hpp : p.Prime)
    (h2 : ∀ e, 2 ≤ e → f (p ^ e) = 0) : ∑' e, f (p ^ e) = 1 + f p := by
  rw [tsum_eq_sum (s := range 2) (fun e he => h2 e (by simp at he; omega))]
  simp [sum_range_succ, hf1]

theorem tsum_prime_pow_real {f : ℕ → ℝ} {p : ℕ} (hf1 : f 1 = 1) (hpp : p.Prime)
    (h2 : ∀ e, 2 ≤ e → f (p ^ e) = 0) : ∑' e, f (p ^ e) = 1 + f p := by
  rw [tsum_eq_sum (s := range 2) (fun e he => h2 e (by simp at he; omega))]
  simp [sum_range_succ, hf1]

theorem abs_hp_le (Z m p : ℕ) (hpp : p.Prime) : |hp Z m p| ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
  have h1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    linarith
  have hpos : 0 < (p : ℝ) - 1 := by linarith
  unfold hp
  split_ifs
  · rw [abs_div, abs_neg, abs_one, abs_of_pos (by positivity)]
  · rw [abs_of_pos (by positivity)]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  · simp; positivity

theorem sum_primes_inv_sq_le (N : ℕ) : ∑ p ∈ Nat.primesBelow N, 1 / ((p : ℝ) - 1) ^ 2 ≤ 2 := by
  rw [← sum_filter_add_sum_filter_not _ (fun p => 3 ≤ p)]
  have h1 := sum_inv_sq_le 3 le_rfl ((Nat.primesBelow N).filter (fun p => 3 ≤ p))
    (fun n hn => (mem_filter.mp hn).2)
  have h2 : ∑ p ∈ (Nat.primesBelow N).filter (fun p => ¬ 3 ≤ p), 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
    have hsub : (Nat.primesBelow N).filter (fun p => ¬ 3 ≤ p) ⊆ {2} := by
      intro p hp
      have := Nat.prime_of_mem_primesBelow (mem_filter.mp hp).1
      have h3 := (mem_filter.mp hp).2
      have := this.two_le
      simp; omega
    calc _ ≤ ∑ p ∈ ({2} : Finset ℕ), 1 / ((p : ℝ) - 1) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 1 := by norm_num
  rw [show (1 : ℝ) / (((3 : ℕ) : ℝ) - 2) = 1 by norm_num] at h1
  linarith

/-- `Σ |h(v)|` converges. -/
theorem summable_norm_hv (Z m : ℕ) : Summable (fun v => ‖hv Z m v‖) := by
  set g : ℕ → ℝ := fun v => ‖hv Z m v‖
  have g1 : g 1 = 1 := by simp [g, hv_one]
  have gmul : ∀ {a b : ℕ}, a.Coprime b → g (a * b) = g a * g b := by
    intro a b h; simp only [g]; rw [hv_mul Z m h, norm_mul]
  have g2 : ∀ p e, p.Prime → 2 ≤ e → g (p ^ e) = 0 := by
    intro p e hp he; simp [g, hv_prime_pow Z m p e hp he]
  have gp : ∀ p, p.Prime → g p ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
    intro p hp; simp only [g]; rw [hv_prime Z m p hp, Complex.norm_real, Real.norm_eq_abs]
    exact abs_hp_le Z m p hp
  have hsp : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ => ‖g (p ^ n)‖) := by
    intro p hp
    apply summable_of_ne_finset_zero (s := range 2)
    intro e he; simp at he; simp [g2 p e hp (by omega)]
  refine summable_of_sum_le (c := Real.exp 2) (fun v => norm_nonneg _) fun u => ?_
  set N := u.sup id + 1
  obtain ⟨-, hS⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := g) g1 gmul hsp N
  have hfac : ∀ p ∈ Nat.primesBelow N, ∑' n : ℕ, g (p ^ n) = 1 + g p := fun p hp =>
    tsum_prime_pow_real g1 (Nat.prime_of_mem_primesBelow hp)
      (fun e he => g2 p e (Nat.prime_of_mem_primesBelow hp) he)
  rw [prod_congr rfl hfac] at hS
  have hle : ∑ x ∈ u, g x ≤ ∏ p ∈ Nat.primesBelow N, (1 + g p) := by
    have e1 : ∑ x ∈ u, g x = ∑ x ∈ u.subtype (· ∈ N.smoothNumbers), g x := by
      rw [sum_subtype_eq_sum_filter]
      symm; apply sum_filter_of_ne
      intro x hx hne
      have hx0 : x ≠ 0 := by rintro rfl; simp [g, hv_zero] at hne
      exact Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hx0)
        (Nat.lt_succ_of_le (le_sup (f := id) hx))
    rw [e1]
    exact sum_le_hasSum _ (fun _ _ => norm_nonneg _) hS
  refine le_trans hle ?_
  calc ∏ p ∈ Nat.primesBelow N, (1 + g p)
      ≤ ∏ p ∈ Nat.primesBelow N, Real.exp (1 / ((p : ℝ) - 1) ^ 2) := by
        refine prod_le_prod₀ (fun p _ => by positivity) fun p hp => ?_
        have := gp p (Nat.prime_of_mem_primesBelow hp)
        linarith [Real.add_one_le_exp (g p), Real.exp_le_exp.mpr this]
    _ = Real.exp (∑ p ∈ Nat.primesBelow N, 1 / ((p : ℝ) - 1) ^ 2) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (sum_primes_inv_sq_le N)

/-- **(7.16), PDF form, as a limit of real partial Euler products.** -/
theorem tendsto_partial (Z m : ℕ) :
    Tendsto (fun n => ((∏ p ∈ Nat.primesBelow n, (1 + hp Z m p) : ℝ) : ℂ)) atTop
      (nhds (hsum Z m)) := by
  have hE := EulerProduct.eulerProduct_hasProd_mulIndicator (f := hv Z m) (hv_one Z m)
    (fun h => hv_mul Z m h) (summable_norm_hv Z m) (hv_zero Z m)
  have hT := hE.tendsto_prod_nat
  unfold hsum
  refine hT.congr fun n => ?_
  simp only [Set.mulIndicator_apply, Set.mem_setOf_eq]
  rw [← prod_filter]
  push_cast
  refine prod_congr (by ext p; simp [Nat.primesBelow]) ?_
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
  rw [tsum_prime_pow (hv_one Z m) hpp (fun e he => hv_prime_pow Z m p e hpp he), hv_prime Z m p hpp]

/-- **`Euler716` PROVED.** -/
theorem euler716 : Euler716 := by
  intro Z m hm
  have hT := tendsto_partial Z m
  set P : ℕ → ℝ := fun n => ∏ p ∈ Nat.primesBelow n, (1 + hp Z m p)
  have hre : Tendsto P atTop (nhds (hsum Z m).re) := by
    have := (Complex.continuous_re.tendsto _).comp hT
    exact this.congr (fun n => Complex.ofReal_re _)
  have him : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (hsum Z m).im) := by
    have := (Complex.continuous_im.tendsto _).comp hT
    exact this.congr (fun n => Complex.ofReal_im _)
  have him0 : (hsum Z m).im = 0 := tendsto_nhds_unique him tendsto_const_nhds
  refine ⟨(hsum Z m).re, Complex.ext (by simp) (by simp [him0]), ?_⟩
  set T := m.primeFactors.filter (fun p => Z ≤ p)
  refine ge_of_tendsto hre (eventually_atTop.mpr ⟨m + 1, fun n hn => ?_⟩)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hTsub : T ⊆ Nat.primesBelow n := by
    intro p hp
    have h1 := (mem_filter.mp hp).1
    have hpp := Nat.prime_of_mem_primeFactors h1
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) (Nat.dvd_of_mem_primeFactors h1)
    simp [Nat.primesBelow, hpp]; omega
  simp only [P]
  rw [← prod_sdiff hTsub]
  have hTval : ∏ p ∈ T, (1 + hp Z m p) = ∏ p ∈ T, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    apply prod_congr rfl; intro p hq
    have h1 := mem_filter.mp hq
    unfold hp; rw [if_pos h1.2, if_pos (Nat.dvd_of_mem_primeFactors h1.1)]; ring
  rw [hTval]
  have hT0 : 0 ≤ ∏ p ∈ T, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    refine prod_nonneg fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).two_le
    have h2 : (1 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast this
      linarith
    have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  have hrest : 1 ≤ ∏ p ∈ Nat.primesBelow n \ T, (1 + hp Z m p) := by
    have := prod_le_prod₀ (s := Nat.primesBelow n \ T) (f := fun _ => (1 : ℝ))
      (g := fun p => 1 + hp Z m p) (fun _ _ => zero_le_one) ?_
    · simpa using this
    intro p hq
    have hp' := mem_sdiff.mp hq
    have hpp := Nat.prime_of_mem_primesBelow hp'.1
    have h2 : (1 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      linarith
    unfold hp
    split_ifs with hZ hd
    · exfalso; apply hp'.2
      exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp, hd, hm0⟩, hZ⟩
    · have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 3 := by positivity
      linarith
    · simp
  nlinarith

/-- **MajorLower, CONDITIONAL ON `Major618 A B`, `Tail72 A B`, `Lemma82`** only. -/
theorem majorLower_of_three (A B : ℕ) (hA : 1 ≤ A) (hB : 36 * A + 3 ≤ B)
    (h618 : Major618 A B) (h72 : Tail72 A B) (h82 : Lemma82) :
    MajorLower A B (9 * (A : ℝ) + 1) :=
  majorLower_of_inputs A B hA hB h618 h72 h82 euler716

/-! ### Vacuity tests -/

/-- `c_3(1) = -1` and `c_3(3) = 2`, genuine instances of `ram_prime`. -/
example : ram 3 1 = -1 := by rw [ram_prime 3 1 Nat.prime_three]; norm_num
example : ram 3 3 = 2 := by rw [ram_prime 3 3 Nat.prime_three]; norm_num

/-- `c_{15}(1) = c_3(1) c_5(1)`, a genuine CRT instance. -/
example : ram 15 1 = ram 3 1 * ram 5 1 := ram_mul 3 5 1 (by norm_num) (by norm_num) (by norm_num)

/-- `euler716` at `Z = 4`, `m = 35`: `Σ h` is real and at least `(1 - 1/16)(1 - 1/36)`. -/
example : ∃ x : ℝ, hsum 4 35 = (x : ℂ) ∧
    ∏ p ∈ (35 : ℕ).primeFactors.filter (fun p => 4 ≤ p), (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤ x :=
  euler716 4 35 ⟨17, by norm_num⟩

end LeanLab.SparseTernary.LocalFactors

#print axioms LeanLab.SparseTernary.LocalFactors.ram_mul
#print axioms LeanLab.SparseTernary.LocalFactors.ram_prime
#print axioms LeanLab.SparseTernary.LocalFactors.summable_norm_hv
#print axioms LeanLab.SparseTernary.LocalFactors.euler716
#print axioms LeanLab.SparseTernary.LocalFactors.majorLower_of_three
