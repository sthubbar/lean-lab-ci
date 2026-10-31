/-
P0086 Basak, Bhat, Dong, Zaharescu 2024, arXiv 2409.08968 v1, Section 7, displays (7.2)-(7.15).
`Tail72 A B` of MajorArcs.lean PROVED unconditionally, as `tail72`, for every `A` and `B`.

Plain math, our own write-up of the paper's Section 7. Write `n = q_0`, squarefree.
1. `fq_split`. For every `q ≥ 1`, with `w = (q, q_0)` and `v = q / w`,
   `f(q) = f(w) h(v)`, displays (7.3)-(7.15): `f = g * h`.
   * If `(v, q_0) > 1`, some prime `p ∣ q_0` has `p² ∣ q`; then `p² ∣ q_ℓ` for every `ℓ`
     because `p² ∤ q_0`, so every `μ(q_ℓ) = 0` and `f(q) = 0 = h(v)` (`fq_zero_of`).
   * If `(v, q_0) = 1`: `q_ℓ = v · q_0/(q_0, a q_0/w + ℓ v)` (`qell_split`), so
     `inner(q, a) = μ(v)/φ(v) · inner(w, a v̄)` with `v v̄ ≡ 1 mod q_0` (`inner_split`), by the shift
     `ℓ ↦ a q_0/w + ℓ v mod q_0`, the Farey grouping and `Ksum` of Lemma82Alt.lean; then CRT
     (`sum_U_crt`) splits `a ↔ (x, y)`, `a ≡ x v + y w`, and gives `f(wv) = f(w) h(v)` (`fq_mul`).
2. `sum_fq_split`. `Σ_{q ≤ N} f(q) = Σ_{w ∣ q_0} f(w) Σ_{v ≤ N/w} h(v)`.
3. `tail_hv`. `Σ_{X < v ≤ M} |h(v)| ≤ 2e⁴/(X+1)`: `|h(v)| ≤ μ²(v)/φ(v)²`, and for squarefree `v`,
   `v²/φ(v)² = Σ_{d ∣ v} c(d)` with `c = ∏_{p ∣ d} ((p/(p-1))² - 1)`; swapping sums,
   `Σ_{k > X/d} 1/k² ≤ 2d/(X+1)` (Mathlib `sum_Ioo_inv_sq_le`), and `Σ_{d ≤ M, sqf} c(d)/d ≤ e⁴`.
4. `norm_fq_le`. `|f(w)| ≤ q_0⁴` for `w ≤ q_0`, from `|μ/φ| ≤ 1` and `#R_0 ≤ q_0`.
5. `tail72`. `|𝔖_P(m) - G(q_0) Σ_v h(v)| ≤ Σ_w |f(w)| · 2e⁴ q_0 / P ≤ 2e⁴ q_0⁶ / P
   ≤ 2e⁴ (log u)^{27A - B}`, using `q_0² ≤ (log u)^{9A}` (`q0_sq_le`). This is (7.2).

Consequence: `repProp_of_two`, `RepProp A` for `A ≥ 1`, `B ≥ 36A + 3`, `B ≥ 28A + 13`,
CONDITIONAL ON `Minor516W A B` and `Major618 A B` only.

AI-written Lean code, Claude, run 20261021T0503Z-11296, unit U-1362. Checked only by the Lean
kernel. Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.SparseTernary.Lemma82Alt

open Finset Filter Real
open scoped Classical

noncomputable section
namespace LeanLab.SparseTernary.Tail72Proof

open LeanLab.SparseTernary LeanLab.SparseTernary.Section4 LeanLab.SparseTernary.MajorArcs
open LeanLab.SparseTernary.LocalFactors LeanLab.SparseTernary.Lemma82Proof

/-! ### Helpers -/

theorem norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  have : (2 * Real.pi * Complex.I * x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem ee_dvd (n : ℕ) (hn : 0 < n) (s t : ℤ) (hd : (n : ℤ) ∣ t - s) :
    ee ((s : ℝ) / n) = ee ((t : ℝ) / n) := by
  obtain ⟨c, hc⟩ := hd
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : (t : ℝ) = s + n * c := by
    have := congrArg (Int.cast (R := ℝ)) hc; push_cast at this; linarith
  have h2 : (t : ℝ) / n = (s : ℝ) / n + ((c : ℤ) : ℝ) := by rw [h1]; field_simp
  rw [h2, ee_add, ee_int, mul_one]

theorem sqf_q0 (Z : ℕ) : Squarefree (q0 Z) := by
  unfold q0
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro a ha b hb hab
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (Nat.prime_of_mem_primesBelow ha)
      (Nat.prime_of_mem_primesBelow hb)).mpr hab)
  · intro i hi; exact (Nat.prime_of_mem_primesBelow hi).squarefree

/-- An inverse of `v` mod `n`, written `v v̄ = 1 + n s`. -/
theorem exists_inv (v n : ℕ) (hv : 0 < v) (h : v.Coprime n) (hn : 0 < n) :
    ∃ vb s : ℕ, v * vb = 1 + n * s := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have : n = 1 := by omega
    subst this
    exact ⟨1, v - 1, by omega⟩
  · obtain ⟨b, -, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime h h2
    refine ⟨b, v * b / n, ?_⟩
    have := Nat.mod_add_div (v * b) n
    rw [hb] at this; omega

/-- **CRT for sums over reduced residues.** -/
theorem sum_U_crt (v w : ℕ) (hv : 1 ≤ v) (hw : 1 ≤ w) (hvw : v.Coprime w) (F : ℕ → ℂ)
    (G : ℕ → ℕ → ℂ) (hF : ∀ a x y, a ≡ x * w + y * v [MOD v * w] → F a = G x y) :
    ∑ a ∈ U (v * w), F a = ∑ x ∈ U v, ∑ y ∈ U w, G x y := by
  set n := v * w with hn
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by positivity)
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
  rw [← sum_product' (f := G)]
  symm
  refine sum_bij (fun t _ => φ t) hmem (fun a ha b hb h => hinj a ha b hb h) ?_ ?_
  · intro b hb
    obtain ⟨a, ha, h⟩ := hsurj b hb
    exact ⟨a, ha, h.symm⟩
  · intro t ht
    exact (hF (φ t) t.1 t.2 (hmodφ t ht)).symm

/-- Shifting by a unit multiple mod `n`. -/
theorem sum_shift_mul (n c v : ℕ) (hn : 0 < n) (hv : v.Coprime n) (h : ℕ → ℂ) :
    ∑ ℓ ∈ range n, h ((c + ℓ * v) % n) = ∑ b ∈ range n, h b := by
  have hmem : ∀ ℓ ∈ range n, (c + ℓ * v) % n ∈ range n :=
    fun ℓ _ => mem_range.mpr (Nat.mod_lt _ hn)
  have hinj : ∀ a ∈ range n, ∀ b ∈ range n, (c + a * v) % n = (c + b * v) % n → a = b := by
    intro a ha b hb e
    have h1 : a * v ≡ b * v [MOD n] := Nat.ModEq.add_left_cancel' c e
    have h' : a ≡ b [MOD n] :=
      Nat.ModEq.cancel_right_of_coprime (Nat.Coprime.gcd_eq_one hv.symm) h1
    rw [mem_range] at ha hb
    unfold Nat.ModEq at h'; rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
  have hsurj := surj_on_of_inj_on_of_card_le (fun ℓ _ => (c + ℓ * v) % n) hmem
    (fun a b ha hb e => hinj a ha b hb e) le_rfl
  exact sum_bij (fun ℓ _ => (c + ℓ * v) % n) hmem (fun a ha b hb e => hinj a ha b hb e)
    (fun b hb => by obtain ⟨a, ha, e⟩ := hsurj b hb; exact ⟨a, ha, e.symm⟩) (fun _ _ => rfl)

/-! ### Step 1a: the coprime case `(v, q_0) = 1` -/

/-- `q_ℓ` for `q = w v`, `w ∣ q_0`, `(v, q_0) = 1`. -/
theorem qell_split (Z w v a ℓ : ℕ) (hw : w ∣ q0 Z) (hw0 : 0 < w) (hvc : v.Coprime (q0 Z))
    (ha : a.Coprime v) :
    qell Z (w * v) a ℓ = v * (q0 Z / Nat.gcd (q0 Z) (a * (q0 Z / w) + ℓ * v)) := by
  obtain ⟨k, hk⟩ := id hw
  have hkd : q0 Z / w = k := by rw [hk, Nat.mul_div_cancel_left _ hw0]
  rw [hkd]
  unfold qell
  have e1 : a * q0 Z + ℓ * (w * v) = w * (a * k + ℓ * v) := by rw [hk]; ring
  have e2 : w * v * q0 Z = w * (v * q0 Z) := by ring
  rw [e1, e2, Nat.gcd_mul_left]
  have hkn : k ∣ q0 Z := ⟨w, by rw [hk]; ring⟩
  have hcop : v.Coprime (a * k + ℓ * v) := by
    rw [Nat.coprime_add_mul_right_right]
    exact Nat.Coprime.mul_right ha.symm (Nat.Coprime.coprime_dvd_right hkn hvc)
  rw [Nat.Coprime.gcd_mul_left_cancel (q0 Z) hcop, Nat.mul_div_mul_left _ _ hw0,
    Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _)]

/-- The `ℓ` sum with a unit multiplier `v`: it equals `κ Σ_{r ∈ R_0} e(a v̄ r / w)`. -/
theorem J_eq (Z w v a vb s : ℕ) (hw : w ∣ q0 Z) (hw0 : 0 < w) (hvc : v.Coprime (q0 Z))
    (hvb : v * vb = 1 + q0 Z * s) :
    ∑ ℓ ∈ range (q0 Z), (muphi (q0 Z / Nat.gcd (q0 Z) (a * (q0 Z / w) + ℓ * v)) : ℂ) *
        ∑ r ∈ R0 Z, ee (-((ℓ : ℝ) * r / q0 Z)) =
      ((kap Z : ℝ) : ℂ) * ∑ r ∈ R0 Z, ee (((a * vb : ℕ) : ℝ) * r / w) := by
  obtain ⟨k, hk⟩ := id hw
  have hkdiv : q0 Z / w = k := by rw [hk, Nat.mul_div_cancel_left _ hw0]
  rw [hkdiv]
  have hswap : ∑ ℓ ∈ range (q0 Z), (muphi (q0 Z / Nat.gcd (q0 Z) (a * k + ℓ * v)) : ℂ) *
        ∑ r ∈ R0 Z, ee (-((ℓ : ℝ) * r / q0 Z)) =
      ∑ r ∈ R0 Z, ∑ ℓ ∈ range (q0 Z), (muphi (q0 Z / Nat.gcd (q0 Z) (a * k + ℓ * v)) : ℂ) *
        ee (-((ℓ : ℝ) * r / q0 Z)) := by
    simp_rw [mul_sum]; exact sum_comm
  rw [hswap, mul_sum]
  refine sum_congr rfl fun r hr => ?_
  have hrc : r.Coprime (q0 Z) := (mem_filter.mp hr).2.1
  have hvbc : vb.Coprime (q0 Z) := by
    have : (v * vb).Coprime (q0 Z) := by
      rw [hvb, Nat.coprime_add_mul_left_left]; exact Nat.coprime_one_left _
    exact Nat.Coprime.coprime_mul_left this
  have hterm : ∀ ℓ, (muphi (q0 Z / Nat.gcd (q0 Z) (a * k + ℓ * v)) : ℂ) *
      ee (-((ℓ : ℝ) * r / q0 Z)) =
      ee (((a * vb : ℕ) : ℝ) * r / w) *
        ((muphi (q0 Z / Nat.gcd (q0 Z) ((a * k + ℓ * v) % q0 Z)) : ℂ) *
        ee ((((a * k + ℓ * v) % q0 Z : ℕ) : ℝ) * (((-((vb * r : ℕ) : ℤ)) : ℤ) : ℝ) / q0 Z)) := by
    intro ℓ
    rw [gcd_mod]
    set b := (a * k + ℓ * v) % q0 Z
    set t := (a * k + ℓ * v) / q0 Z
    have e1 : b + q0 Z * t = a * k + ℓ * v := Nat.mod_add_div _ _
    have e1' : (b : ℝ) = a * k + ℓ * v - q0 Z * t := by
      have := congrArg (Nat.cast (R := ℝ)) e1; push_cast at this; linarith
    have hs : (v : ℝ) * vb = 1 + q0 Z * s := by
      have := congrArg (Nat.cast (R := ℝ)) hvb; push_cast at this; linarith
    have hl : (ℓ : ℝ) * r = ℓ * r * (v * vb) - ℓ * r * q0 Z * s := by rw [hs]; ring
    have hnR : (q0 Z : ℝ) = w * k := by rw [hk]; push_cast; ring
    have hw0' : (w : ℝ) ≠ 0 := by exact_mod_cast hw0.ne'
    have hk0 : (k : ℝ) ≠ 0 := by
      have : (q0 Z : ℝ) ≠ 0 := by exact_mod_cast (q0_pos Z).ne'
      intro h0; rw [hnR, h0, mul_zero] at this; exact this rfl
    have key : -((ℓ : ℝ) * r / q0 Z) = ((a * vb : ℕ) : ℝ) * r / w +
        ((b : ℝ) * (((-((vb * r : ℕ) : ℤ)) : ℤ) : ℝ) / q0 Z +
          ((((ℓ * r * s : ℕ) : ℤ) - ((t * vb * r : ℕ) : ℤ) : ℤ) : ℝ)) := by
      rw [hl, e1', hnR]; push_cast; field_simp; ring
    rw [key, ee_add, ee_add, ee_int, mul_one]
    ring
  rw [sum_congr rfl (fun ℓ _ => hterm ℓ), ← mul_sum]
  rw [sum_shift_mul (q0 Z) (a * k) v (q0_pos Z) hvc
    (fun b => (muphi (q0 Z / Nat.gcd (q0 Z) b) : ℂ) *
      ee ((b : ℝ) * (((-((vb * r : ℕ) : ℤ)) : ℤ) : ℝ) / q0 Z))]
  rw [← farey (q0 Z) (q0_pos Z) (fun d => (muphi d : ℂ)) (-((vb * r : ℕ) : ℤ))]
  have hram : ∑ d ∈ (q0 Z).divisors, (muphi d : ℂ) *
      ∑ c ∈ U d, ee ((c : ℝ) * (((-((vb * r : ℕ) : ℤ)) : ℤ) : ℝ) / d) =
      ∑ d ∈ (q0 Z).divisors, (muphi d : ℂ) * ram d (vb * r) := by
    refine sum_congr rfl fun d _ => ?_
    unfold ram
    congr 1
    refine sum_congr rfl fun c _ => ?_
    congr 1; push_cast; ring
  rw [hram, Ksum Z (vb * r) (Nat.Coprime.mul_left hvbc hrc)]
  ring

/-- **`inner(w v, a) = μ(v)/φ(v) · inner(w, a v̄)`.** -/
theorem inner_split (Z w v a vb s : ℕ) (hw : w ∣ q0 Z) (hw0 : 0 < w)
    (hvc : v.Coprime (q0 Z)) (ha : a.Coprime v) (hvb : v * vb = 1 + q0 Z * s) :
    MajorArcs.inner Z (w * v) a = (muphi v : ℂ) * MajorArcs.inner Z w (a * vb) := by
  rw [inner_eq Z w (a * vb) hw hw0, ← J_eq Z w v a vb s hw hw0 hvc hvb]
  unfold MajorArcs.inner
  rw [mul_sum]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [qell_split Z w v a ℓ hw hw0 hvc ha,
    muphi_mul (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)) hvc)]
  push_cast; ring

/-- `μ(n)³ = μ(n)`. -/
theorem moebius_cube (n : ℕ) : ((ArithmeticFunction.moebius n : ℤ) : ℂ) ^ 3 =
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) := by
  have h := abs_le.mp (ArithmeticFunction.abs_moebius_le_one (n := n))
  have : ArithmeticFunction.moebius n = -1 ∨ ArithmeticFunction.moebius n = 0 ∨
      ArithmeticFunction.moebius n = 1 := by omega
  rcases this with h1 | h1 | h1 <;> rw [h1] <;> norm_num

/-- **`f(w v) = f(w) h(v)`** for `w ∣ q_0`, `(v, q_0) = 1`. -/
theorem fq_mul (Z m w v : ℕ) (hw : w ∣ q0 Z) (hw0 : 0 < w) (hv0 : 0 < v)
    (hvc : v.Coprime (q0 Z)) : fq Z m (w * v) = fq Z m w * hv Z m v := by
  obtain ⟨vb, s, hvb⟩ := exists_inv v (q0 Z) hv0 hvc (q0_pos Z)
  obtain ⟨k, hk⟩ := id hw
  have hwv : w.Coprime v := (Nat.Coprime.coprime_dvd_right hw hvc).symm
  -- rewrite the inner sums
  have h1 : ∑ a ∈ U (w * v), ee (-((a : ℝ) * m / ((w * v : ℕ) : ℝ))) *
        MajorArcs.inner Z (w * v) a ^ 3 =
      ∑ a ∈ U (w * v), ee (-((a : ℝ) * m / ((w * v : ℕ) : ℝ))) *
        ((muphi v : ℂ) * MajorArcs.inner Z w (a * vb)) ^ 3 := by
    refine sum_congr rfl fun a ha => ?_
    have hac : a.Coprime (w * v) := (mem_filter.mp ha).2
    rw [inner_split Z w v a vb s hw hw0 hvc (Nat.Coprime.coprime_mul_left_right hac) hvb]
  have hcrt := sum_U_crt w v hw0 hv0 hwv
    (fun a => ee (-((a : ℝ) * m / ((w * v : ℕ) : ℝ))) * ((muphi v : ℂ) * MajorArcs.inner Z w (a * vb)) ^ 3)
    (fun x y => ee (-((x : ℝ) * m / w)) * ee (-((y : ℝ) * m / v)) *
      ((muphi v : ℂ) * MajorArcs.inner Z w x) ^ 3) (by
    intro a x y hmod
    have hd : ((w * v : ℕ) : ℤ) ∣ ((x * v + y * w : ℕ) : ℤ) - (a : ℤ) :=
      (Nat.modEq_iff_dvd.mp hmod)
    have hwv0 : 0 < w * v := Nat.mul_pos hw0 hv0
    -- the phase
    have hph : ee (-((a : ℝ) * m / ((w * v : ℕ) : ℝ))) =
        ee (-((x : ℝ) * m / w)) * ee (-((y : ℝ) * m / v)) := by
      have L : -((a : ℝ) * m / ((w * v : ℕ) : ℝ)) =
          (((-((a * m : ℕ) : ℤ)) : ℤ) : ℝ) / ((w * v : ℕ) : ℝ) := by push_cast; ring
      have R : -((x : ℝ) * m / w) + -((y : ℝ) * m / v) =
          (((-(((x * v + y * w) * m : ℕ) : ℤ)) : ℤ) : ℝ) / ((w * v : ℕ) : ℝ) := by
        have hw' : (w : ℝ) ≠ 0 := by exact_mod_cast hw0.ne'
        have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv0.ne'
        push_cast; field_simp; ring
      rw [← ee_add, R, L]
      apply ee_dvd _ hwv0
      have : (-(((x * v + y * w) * m : ℕ) : ℤ)) - (-((a * m : ℕ) : ℤ)) =
          -((((x * v + y * w : ℕ) : ℤ) - (a : ℤ)) * (m : ℤ)) := by push_cast; ring
      rw [this]
      exact dvd_neg.mpr (dvd_mul_of_dvd_left hd _)
    -- the inner sum
    have hin : MajorArcs.inner Z w (a * vb) = MajorArcs.inner Z w x := by
      rw [inner_eq Z w (a * vb) hw hw0, inner_eq Z w x hw hw0]
      congr 1
      refine sum_congr rfl fun r _ => ?_
      have hdw : (w : ℤ) ∣ ((x * v + y * w : ℕ) : ℤ) - (a : ℤ) :=
        dvd_trans ⟨(v : ℤ), by push_cast; ring⟩ hd
      obtain ⟨c1, hc1⟩ := hdw
      have hs' : ((v : ℤ) * vb) = 1 + w * k * s := by
        have := congrArg (Nat.cast (R := ℤ)) hvb; push_cast at this; rw [this, hk]; push_cast; ring
      have L : ((a * vb : ℕ) : ℝ) * r / w = (((a * vb * r : ℕ) : ℤ) : ℝ) / w := by
        push_cast; ring
      have R : (x : ℝ) * r / w = (((x * r : ℕ) : ℤ) : ℝ) / w := by push_cast; ring
      rw [L, R]
      apply ee_dvd _ hw0
      refine ⟨(r : ℤ) * (-((x : ℤ) * k * s) - (y : ℤ) * vb + c1 * vb), ?_⟩
      push_cast at hc1 ⊢
      linear_combination ((r : ℤ) * vb) * hc1 - ((r : ℤ) * x) * hs'
    rw [hph, hin])
  beta_reduce at hcrt
  unfold fq
  change (1 : ℂ) / (q0 Z : ℂ) ^ 3 * ∑ a ∈ U (w * v), ee (-((a : ℝ) * m / ((w * v : ℕ) : ℝ))) *
      MajorArcs.inner Z (w * v) a ^ 3 = (1 / (q0 Z : ℂ) ^ 3 * ∑ a ∈ U w,
      ee (-((a : ℝ) * m / (w : ℝ))) * MajorArcs.inner Z w a ^ 3) * hv Z m v
  rw [h1, hcrt, hv_eq, if_pos hvc]
  have h2 : ∑ x ∈ U w, ∑ y ∈ U v, ee (-((x : ℝ) * m / w)) * ee (-((y : ℝ) * m / v)) *
      ((muphi v : ℂ) * MajorArcs.inner Z w x) ^ 3 =
      (muphi v : ℂ) ^ 3 * (∑ x ∈ U w, ee (-((x : ℝ) * m / w)) * MajorArcs.inner Z w x ^ 3) * ram v m := by
    unfold ram
    rw [mul_sum (s := U w), sum_mul_sum]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    ring
  rw [h2]
  have hM : (muphi v : ℂ) ^ 3 = ((ArithmeticFunction.moebius v : ℤ) : ℂ) / (v.totient : ℂ) ^ 3 := by
    unfold muphi
    push_cast
    rw [div_pow, moebius_cube]
  rw [hM]
  ring

/-! ### Step 1b: the case `(v, q_0) > 1` -/

theorem pp_dvd_aux {p g x : ℕ} (hp : p.Prime) (h : p ^ 3 ∣ g * x) (hg : ¬ p * p ∣ g) :
    p * p ∣ x := by
  by_cases hpg : p ∣ g
  · obtain ⟨g', rfl⟩ := hpg
    have hg' : ¬ p ∣ g' := fun h' => hg (mul_dvd_mul_left p h')
    have h2 : p * p ∣ g' * x := by
      have e : p ^ 3 = p * (p * p) := by ring
      rw [e, mul_assoc] at h
      exact Nat.dvd_of_mul_dvd_mul_left hp.pos h
    have hc : Nat.Coprime p g' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hg'
    exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.mul_left hc hc) h2
  · have hc : Nat.Coprime (p ^ 3) g :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpg)
    have h3 := Nat.Coprime.dvd_of_dvd_mul_left hc h
    exact dvd_trans ⟨p, by ring⟩ h3

/-- If `p ∣ q_0` and `p² ∣ q`, then `f(q) = 0`: every `μ(q_ℓ)` vanishes. -/
theorem fq_zero_of (Z m q p : ℕ) (hq : 0 < q) (hp : p.Prime) (hpq : p * p ∣ q)
    (hpn : p ∣ q0 Z) : fq Z m q = 0 := by
  have hsq := sqf_q0 Z
  unfold fq
  rw [sum_eq_zero, mul_zero]
  intro a ha
  have hac : a.Coprime q := (mem_filter.mp ha).2
  have hpa : ¬ p ∣ a := by
    intro h
    have : p ∣ Nat.gcd a q := Nat.dvd_gcd h (dvd_trans (dvd_mul_right p p) hpq)
    rw [hac.gcd_eq_one] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hinner : MajorArcs.inner Z q a = 0 := by
    unfold MajorArcs.inner
    refine sum_eq_zero fun ℓ _ => ?_
    have hmu : muphi (qell Z q a ℓ) = 0 := by
      unfold muphi qell
      set g := Nat.gcd (q * q0 Z) (a * q0 Z + ℓ * q)
      have hgq : g * (q * q0 Z / g) = q * q0 Z := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have h3 : p ^ 3 ∣ g * (q * q0 Z / g) := by
        rw [hgq, show p ^ 3 = p * p * p by ring]; exact mul_dvd_mul hpq hpn
      have hg : ¬ p * p ∣ g := by
        intro h
        have h1 : p * p ∣ a * q0 Z + ℓ * q := dvd_trans h (Nat.gcd_dvd_right _ _)
        have h2 : p * p ∣ ℓ * q := dvd_mul_of_dvd_right hpq ℓ
        have h4 : p * p ∣ a * q0 Z := (Nat.dvd_add_left h2).mp h1
        have hc : Nat.Coprime (p * p) a := by
          have := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpa
          exact Nat.Coprime.mul_left this this
        have h5 := Nat.Coprime.dvd_of_dvd_mul_left hc h4
        exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) h5
      have hdiv := pp_dvd_aux hp h3 hg
      have hns : ¬ Squarefree (q * q0 Z / g) :=
        fun hs => (Nat.squarefree_iff_prime_squarefree.mp hs p hp) hdiv
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]
      simp
    rw [hmu]; simp
  rw [hinner]; simp

/-- **`f(q) = f((q, q_0)) h(q / (q, q_0))`**, displays (7.3)-(7.15). PROVED. -/
theorem fq_split (Z m q : ℕ) (hq : 0 < q) :
    fq Z m q = fq Z m (Nat.gcd q (q0 Z)) * hv Z m (q / Nat.gcd q (q0 Z)) := by
  have hw0 : 0 < Nat.gcd q (q0 Z) := Nat.gcd_pos_of_pos_left _ hq
  have hwq : Nat.gcd q (q0 Z) ∣ q := Nat.gcd_dvd_left _ _
  have hqwv : q = Nat.gcd q (q0 Z) * (q / Nat.gcd q (q0 Z)) := (Nat.mul_div_cancel' hwq).symm
  have hv0 : 0 < q / Nat.gcd q (q0 Z) := Nat.div_pos (Nat.le_of_dvd hq hwq) hw0
  by_cases hvc : (q / Nat.gcd q (q0 Z)).Coprime (q0 Z)
  · conv_lhs => rw [hqwv]
    exact fq_mul Z m _ _ (Nat.gcd_dvd_right _ _) hw0 hv0 hvc
  · rw [hv_eq, if_neg hvc, mul_zero]
    obtain ⟨p, hp, hpv, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hvc
    have hpq : p ∣ q := dvd_trans hpv (Nat.div_dvd_of_dvd hwq)
    have hpw : p ∣ Nat.gcd q (q0 Z) := Nat.dvd_gcd hpq hpn
    exact fq_zero_of Z m q p hq hp (by rw [hqwv]; exact mul_dvd_mul hpw hpv) hpn

/-! ### Step 2: the partial singular series -/

theorem gcd_mul_coprime {Z w v : ℕ} (hw : w ∣ q0 Z) (hvc : v.Coprime (q0 Z)) :
    Nat.gcd (w * v) (q0 Z) = w := by
  rw [Nat.Coprime.gcd_mul_right_cancel w hvc, Nat.gcd_eq_left hw]

/-- **`Σ_{q ≤ N} f(q) = Σ_{w ∣ q_0} f(w) Σ_{v ≤ N/w} h(v)`.** PROVED. -/
theorem sum_fq_split (Z m N : ℕ) :
    ∑ q ∈ Icc 1 N, fq Z m q =
      ∑ w ∈ (q0 Z).divisors, fq Z m w * ∑ v ∈ Icc 1 (N / w), hv Z m v := by
  simp_rw [mul_sum]
  rw [sum_sigma']
  symm
  have hcop : ∀ v, hv Z m v ≠ 0 → v.Coprime (q0 Z) := by
    intro v h; by_contra hc; rw [hv_eq, if_neg hc] at h; exact h rfl
  refine sum_bij_ne_zero (fun x _ _ => x.1 * x.2) ?_ ?_ ?_ ?_
  · rintro ⟨w, v⟩ hx _
    simp only [mem_sigma] at hx
    obtain ⟨hw, hv⟩ := hx
    have hw0 := Nat.pos_of_mem_divisors hw
    rw [mem_Icc] at hv ⊢
    refine ⟨Nat.mul_pos hw0 hv.1, ?_⟩
    have := (Nat.le_div_iff_mul_le hw0).mp hv.2
    simpa [mul_comm] using this
  · rintro ⟨w, v⟩ hx hne ⟨w', v'⟩ hx' hne' he
    simp only at he hne hne'
    simp only [mem_sigma] at hx hx'
    have hc := hcop v (right_ne_zero_of_mul hne)
    have hc' := hcop v' (right_ne_zero_of_mul hne')
    have e1 : w = w' := by
      rw [← gcd_mul_coprime (Nat.dvd_of_mem_divisors hx.1) hc,
        ← gcd_mul_coprime (Nat.dvd_of_mem_divisors hx'.1) hc', he]
    subst e1
    have hw0 := Nat.pos_of_mem_divisors hx.1
    have e2 : v = v' := Nat.eq_of_mul_eq_mul_left hw0 he
    subst e2
    rfl
  · intro q hq hne
    have hq1 := (mem_Icc.mp hq).1
    have hq0 : 0 < q := hq1
    rw [fq_split Z m q hq0] at hne
    have hc := hcop _ (right_ne_zero_of_mul hne)
    have hw0 : 0 < Nat.gcd q (q0 Z) := Nat.gcd_pos_of_pos_left _ hq0
    have hwq : Nat.gcd q (q0 Z) ∣ q := Nat.gcd_dvd_left _ _
    have hqwv : Nat.gcd q (q0 Z) * (q / Nat.gcd q (q0 Z)) = q := Nat.mul_div_cancel' hwq
    refine ⟨⟨Nat.gcd q (q0 Z), q / Nat.gcd q (q0 Z)⟩, ?_, hne, hqwv⟩
    rw [mem_sigma]
    refine ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, (q0_pos Z).ne'⟩, ?_⟩
    rw [mem_Icc]
    refine ⟨Nat.div_pos (Nat.le_of_dvd hq0 hwq) hw0, ?_⟩
    rw [Nat.le_div_iff_mul_le hw0, mul_comm, hqwv]
    exact (mem_Icc.mp hq).2
  · rintro ⟨w, v⟩ hx hne
    simp only at hne ⊢
    simp only [mem_sigma] at hx
    have hw0 := Nat.pos_of_mem_divisors hx.1
    have hv0 : 0 < v := (mem_Icc.mp hx.2).1
    have hc := hcop v (right_ne_zero_of_mul hne)
    rw [fq_split Z m (w * v) (Nat.mul_pos hw0 hv0),
      gcd_mul_coprime (Nat.dvd_of_mem_divisors hx.1) hc, Nat.mul_div_cancel_left _ hw0]


/-! ### Step 3: the tail of `Σ |h(v)|` -/

/-- `ff(p) = (p/(p-1))² - 1 = (2p-1)/(p-1)²`. -/
def ff (p : ℕ) : ℝ := ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 - 1

/-- `c(d) = ∏_{p ∣ d} ff(p)`. -/
def cc : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors ff

/-- `c'(d) = ∏_{p ∣ d} ff(p)/p`. -/
def cc' : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors (fun p => ff p / p)

theorem ff_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ ff p := by
  unfold ff
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have : 1 ≤ (p : ℝ) / ((p : ℝ) - 1) := by rw [le_div_iff₀ h1]; linarith
  nlinarith

theorem ff_div_le {p : ℕ} (hp : 2 ≤ p) : ff p / p ≤ 2 * (1 / ((p : ℝ) - 1) ^ 2) := by
  unfold ff
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have e : ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 - 1 = (2 * p - 1) / ((p : ℝ) - 1) ^ 2 := by
    field_simp; ring
  rw [e, div_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ((p : ℝ) - 1)]

theorem cc_nonneg (d : ℕ) : 0 ≤ cc d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · unfold cc; rw [ArithmeticFunction.prodPrimeFactors_apply hd.ne']
    exact prod_nonneg fun p hp => ff_nonneg (Nat.prime_of_mem_primeFactors hp).two_le

theorem cc'_nonneg (d : ℕ) : 0 ≤ cc' d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · unfold cc'; rw [ArithmeticFunction.prodPrimeFactors_apply hd.ne']
    exact prod_nonneg fun p hp =>
      div_nonneg (ff_nonneg (Nat.prime_of_mem_primeFactors hp).two_le) (Nat.cast_nonneg _)

theorem sum_cc_divisors {v : ℕ} (hv : Squarefree v) :
    ∑ d ∈ v.divisors, cc d = ∏ p ∈ v.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
  unfold cc
  rw [← (ArithmeticFunction.IsMultiplicative.prodPrimeFactors ff).prodPrimeFactors_one_add_of_squarefree hv]
  refine prod_congr rfl fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  rw [ArithmeticFunction.prodPrimeFactors_apply hpp.ne_zero, hpp.primeFactors, prod_singleton]
  unfold ff; ring

/-- For squarefree `v`, `1/φ(v)² = v⁻² Σ_{d ∣ v} c(d)`. -/
theorem inv_totient_sq {v : ℕ} (hv0 : 0 < v) (hv : Squarefree v) :
    1 / ((v.totient : ℝ)) ^ 2 = (1 / (v : ℝ) ^ 2) * ∑ d ∈ v.divisors, cc d := by
  rw [sum_cc_divisors hv]
  have h1 := Nat.totient_mul_prod_primeFactors v
  have h2 := Nat.prod_primeFactors_of_squarefree hv
  have hQ : ((∏ p ∈ v.primeFactors, (p - 1) : ℕ) : ℝ) = ∏ p ∈ v.primeFactors, ((p : ℝ) - 1) := by
    rw [Nat.cast_prod]; refine prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]; simp
  have hP : ((∏ p ∈ v.primeFactors, p : ℕ) : ℝ) = (v : ℝ) := by rw [h2]
  have hP' : ((∏ p ∈ v.primeFactors, p : ℕ) : ℝ) = ∏ p ∈ v.primeFactors, (p : ℝ) :=
    Nat.cast_prod _ _
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv0.ne'
  have hphi : (v.totient : ℝ) = ∏ p ∈ v.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (Nat.cast (R := ℝ)) h1
    rw [Nat.cast_mul, Nat.cast_mul, hP, hQ] at this
    exact mul_right_cancel₀ hv' (by rw [this]; ring)
  have hQ0 : ∏ p ∈ v.primeFactors, ((p : ℝ) - 1) ≠ 0 := prod_ne_zero_iff.mpr fun p hp => by
    have h := (Nat.prime_of_mem_primeFactors hp).two_le
    have : (2 : ℝ) ≤ p := by exact_mod_cast h
    linarith
  rw [hphi, prod_pow, prod_div_distrib, ← hP', hP]
  field_simp

/-- `|h(v)| ≤ v⁻² Σ_{d ∣ v, sqf} c(d)`. -/
theorem norm_hv_le (Z m v : ℕ) (hv0 : 0 < v) :
    ‖hv Z m v‖ ≤ (1 / (v : ℝ) ^ 2) * ∑ d ∈ v.divisors.filter Squarefree, cc d := by
  have hphi0 : (0 : ℝ) < v.totient := by exact_mod_cast Nat.totient_pos.mpr hv0
  have hR : 0 ≤ (1 / (v : ℝ) ^ 2) * ∑ d ∈ v.divisors.filter Squarefree, cc d :=
    mul_nonneg (by positivity) (sum_nonneg fun d _ => cc_nonneg d)
  have hram : ‖ram v m‖ ≤ v.totient := by
    unfold ram
    calc _ ≤ ∑ a ∈ U v, ‖ee (-((a : ℝ) * m / v))‖ := norm_sum_le _ _
      _ = v.totient := by simp only [norm_ee, sum_const, card_U, nsmul_eq_mul, mul_one]
  rw [hv_eq]
  by_cases hs : Squarefree v
  · have hfil : v.divisors.filter Squarefree = v.divisors :=
      filter_true_of_mem fun d hd => hs.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
    rw [hfil, ← inv_totient_sq hv0 hs]
    split_ifs
    · rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
      have hmu : ‖((ArithmeticFunction.moebius v : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      calc ‖((ArithmeticFunction.moebius v : ℤ) : ℂ)‖ / (v.totient : ℝ) ^ 3 * ‖ram v m‖
          ≤ 1 / (v.totient : ℝ) ^ 3 * v.totient :=
            mul_le_mul (div_le_div_of_nonneg_right hmu (by positivity)) hram (norm_nonneg _)
              (by positivity)
        _ = 1 / (v.totient : ℝ) ^ 2 := by field_simp
    · simp only [norm_zero]; positivity
  · split_ifs
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]; simpa using hR
    · simpa using hR

/-- Swapping `v = d k`. -/
theorem swap_le (X M : ℕ) :
    ∑ v ∈ Ioc X M, (1 / (v : ℝ) ^ 2) * ∑ d ∈ v.divisors.filter Squarefree, cc d ≤
      ∑ d ∈ (Icc 1 M).filter Squarefree, cc d / (d : ℝ) ^ 2 *
        ∑ k ∈ (Icc 1 M).filter (fun k => X < d * k), 1 / (k : ℝ) ^ 2 := by
  have lhs : ∑ v ∈ Ioc X M, (1 / (v : ℝ) ^ 2) * ∑ d ∈ v.divisors.filter Squarefree, cc d =
      ∑ x ∈ (Ioc X M).sigma (fun v => v.divisors.filter Squarefree),
        cc x.2 / ((x.1 : ℝ)) ^ 2 := by
    rw [sum_sigma]; refine sum_congr rfl fun v _ => ?_; rw [mul_sum]
    refine sum_congr rfl fun d _ => ?_; dsimp only; ring
  have rhs : ∑ d ∈ (Icc 1 M).filter Squarefree, cc d / (d : ℝ) ^ 2 *
        ∑ k ∈ (Icc 1 M).filter (fun k => X < d * k), 1 / (k : ℝ) ^ 2 =
      ∑ y ∈ ((Icc 1 M).filter Squarefree).sigma (fun d => (Icc 1 M).filter (fun k => X < d * k)),
        cc y.1 / (((y.1 * y.2 : ℕ) : ℝ)) ^ 2 := by
    rw [sum_sigma]; refine sum_congr rfl fun d _ => ?_; rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_; dsimp only; push_cast; rw [mul_pow]; ring
  rw [lhs, rhs]
  let ψ : (Σ _ : ℕ, ℕ) → (Σ _ : ℕ, ℕ) := fun x => ⟨x.2, x.1 / x.2⟩
  have hdv : ∀ x ∈ (Ioc X M).sigma (fun v => v.divisors.filter Squarefree),
      x.2 ∣ x.1 ∧ 0 < x.2 ∧ x.2 ≤ x.1 ∧ X < x.1 ∧ x.1 ≤ M ∧ Squarefree x.2 := by
    rintro ⟨v, d⟩ hx
    rw [mem_sigma, mem_Ioc, mem_filter] at hx
    obtain ⟨⟨h1, h2⟩, hd, hsq⟩ := hx
    exact ⟨Nat.dvd_of_mem_divisors hd, Nat.pos_of_mem_divisors hd,
      Nat.divisor_le hd, h1, h2, hsq⟩
  have hinj : ∀ x ∈ (Ioc X M).sigma (fun v => v.divisors.filter Squarefree),
      ∀ y ∈ (Ioc X M).sigma (fun v => v.divisors.filter Squarefree), ψ x = ψ y → x = y := by
    rintro ⟨v, d⟩ hx ⟨v', d'⟩ hy he
    simp only [ψ, Sigma.mk.inj_iff, heq_eq_eq] at he
    obtain ⟨rfl, h2⟩ := he
    have a1 := hdv _ hx
    have a2 := hdv _ hy
    simp only at a1 a2
    have : v = v' := by
      rw [← Nat.mul_div_cancel' a1.1, ← Nat.mul_div_cancel' a2.1, h2]
    subst this; rfl
  have hsub : ((Ioc X M).sigma (fun v => v.divisors.filter Squarefree)).image ψ ⊆
      ((Icc 1 M).filter Squarefree).sigma (fun d => (Icc 1 M).filter (fun k => X < d * k)) := by
    intro y hy
    rw [mem_image] at hy
    obtain ⟨⟨v, d⟩, hx, rfl⟩ := hy
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hdv _ hx
    simp only at h1 h2 h3 h4 h5 h6
    simp only [ψ, mem_sigma, mem_filter, mem_Icc]
    refine ⟨⟨⟨h2, by omega⟩, h6⟩, ⟨Nat.div_pos h3 h2, le_trans (Nat.div_le_self _ _) h5⟩, ?_⟩
    rw [Nat.mul_div_cancel' h1]; exact h4
  calc ∑ x ∈ (Ioc X M).sigma (fun v => v.divisors.filter Squarefree), cc x.2 / ((x.1 : ℝ)) ^ 2
      = ∑ x ∈ (Ioc X M).sigma (fun v => v.divisors.filter Squarefree),
          (fun y : (Σ _ : ℕ, ℕ) => cc y.1 / (((y.1 * y.2 : ℕ) : ℝ)) ^ 2) (ψ x) := by
        refine sum_congr rfl fun x hx => ?_
        simp only [ψ]
        rw [Nat.mul_div_cancel' (hdv x hx).1]
    _ = ∑ y ∈ ((Ioc X M).sigma (fun v => v.divisors.filter Squarefree)).image ψ,
          (fun y : (Σ _ : ℕ, ℕ) => cc y.1 / (((y.1 * y.2 : ℕ) : ℝ)) ^ 2) y :=
        (sum_image (f := fun y : (Σ _ : ℕ, ℕ) => cc y.1 / (((y.1 * y.2 : ℕ) : ℝ)) ^ 2) hinj).symm
    _ ≤ _ :=
        sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => div_nonneg (cc_nonneg _) (by positivity))

/-- `Σ_{k ≥ 1, dk > X} 1/k² ≤ 2d/(X+1)`. -/
theorem sum_k_le (X M d : ℕ) (hd : 0 < d) :
    ∑ k ∈ (Icc 1 M).filter (fun k => X < d * k), 1 / (k : ℝ) ^ 2 ≤ 2 * d / ((X : ℝ) + 1) := by
  have hsub : (Icc 1 M).filter (fun k => X < d * k) ⊆ Ioo (X / d) (M + 1) := by
    intro k hk
    rw [mem_filter, mem_Icc] at hk
    rw [mem_Ioo]
    refine ⟨?_, by omega⟩
    exact (Nat.div_lt_iff_lt_mul hd).mpr (by rw [mul_comm]; exact hk.2)
  have h1 : ∑ k ∈ (Icc 1 M).filter (fun k => X < d * k), 1 / (k : ℝ) ^ 2 ≤
      ∑ k ∈ Ioo (X / d) (M + 1), ((k : ℝ) ^ 2)⁻¹ := by
    simp only [one_div]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have h2 := sum_Ioo_inv_sq_le (α := ℝ) (X / d) (M + 1)
  have h3 : (X : ℝ) + 1 ≤ (((X / d : ℕ) : ℝ) + 1) * d := by
    have h := Nat.lt_div_mul_add (a := X) hd
    have : X + 1 ≤ (X / d + 1) * d := by rw [add_mul, one_mul]; omega
    exact_mod_cast this
  have h4 : 2 / (((X / d : ℕ) : ℝ) + 1) ≤ 2 * d / ((X : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- `Σ_{d ≤ M, sqf} c(d)/d ≤ e⁴`. -/
theorem sum_cc_div_le (M : ℕ) : ∑ d ∈ (Icc 1 M).filter Squarefree, cc d / d ≤ Real.exp 4 := by
  have hP : Squarefree (q0 (M + 1)) := sqf_q0 _
  have hpf : (q0 (M + 1)).primeFactors = Nat.primesBelow (M + 1) := by
    unfold q0; exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primesBelow hp)
  have hsub : (Icc 1 M).filter Squarefree ⊆ (q0 (M + 1)).divisors := by
    intro d hd
    rw [mem_filter, mem_Icc] at hd
    rw [Nat.mem_divisors]
    refine ⟨?_, (q0_pos _).ne'⟩
    rw [← Nat.prod_primeFactors_of_squarefree hd.2]
    unfold q0
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have := Nat.le_of_mem_primeFactors hp
    rw [Nat.mem_primesBelow]; exact ⟨by omega, hpp⟩
  have heq : ∀ d ∈ (Icc 1 M).filter Squarefree, cc d / d = cc' d := by
    intro d hd
    rw [mem_filter, mem_Icc] at hd
    have hd0 : d ≠ 0 := by omega
    have hdP : ((d : ℕ) : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd.2]
    unfold cc cc'
    rw [ArithmeticFunction.prodPrimeFactors_apply hd0, ArithmeticFunction.prodPrimeFactors_apply hd0,
      prod_div_distrib, hdP]
  have hc'p : ∀ p ∈ Nat.primesBelow (M + 1), cc' p = ff p / p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    unfold cc'
    rw [ArithmeticFunction.prodPrimeFactors_apply hpp.ne_zero, hpp.primeFactors, prod_singleton]
  calc ∑ d ∈ (Icc 1 M).filter Squarefree, cc d / d
      = ∑ d ∈ (Icc 1 M).filter Squarefree, cc' d := sum_congr rfl heq
    _ ≤ ∑ d ∈ (q0 (M + 1)).divisors, cc' d :=
        sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => cc'_nonneg d)
    _ = ∏ p ∈ (q0 (M + 1)).primeFactors, (1 + cc' p) :=
        ((ArithmeticFunction.IsMultiplicative.prodPrimeFactors _).prodPrimeFactors_one_add_of_squarefree
          hP).symm
    _ = ∏ p ∈ Nat.primesBelow (M + 1), (1 + ff p / p) := by
        rw [hpf]; exact prod_congr rfl fun p hp => by rw [hc'p p hp]
    _ ≤ ∏ p ∈ Nat.primesBelow (M + 1), Real.exp (2 * (1 / ((p : ℝ) - 1) ^ 2)) := by
        refine prod_le_prod₀ (fun p hp => ?_) fun p hp => ?_
        · have := (Nat.prime_of_mem_primesBelow hp).two_le
          have := ff_nonneg this
          positivity
        · have h2 := (Nat.prime_of_mem_primesBelow hp).two_le
          have := ff_div_le h2
          linarith [Real.add_one_le_exp (ff p / p), Real.exp_le_exp.mpr this]
    _ = Real.exp (∑ p ∈ Nat.primesBelow (M + 1), 2 * (1 / ((p : ℝ) - 1) ^ 2)) :=
        (Real.exp_sum _ _).symm
    _ ≤ Real.exp 4 := by
        apply Real.exp_le_exp.mpr
        rw [← mul_sum]
        have := sum_primes_inv_sq_le (M + 1)
        linarith

/-- **The tail of `Σ |h(v)|`**: `Σ_{X < v ≤ M} |h(v)| ≤ 2e⁴/(X+1)`. PROVED. -/
theorem tail_hv (Z m X M : ℕ) :
    ∑ v ∈ Ioc X M, ‖hv Z m v‖ ≤ 2 * Real.exp 4 / ((X : ℝ) + 1) := by
  have hX : (0 : ℝ) < (X : ℝ) + 1 := by positivity
  calc ∑ v ∈ Ioc X M, ‖hv Z m v‖
      ≤ ∑ v ∈ Ioc X M, (1 / (v : ℝ) ^ 2) * ∑ d ∈ v.divisors.filter Squarefree, cc d :=
        sum_le_sum fun v hv => norm_hv_le Z m v (by rw [mem_Ioc] at hv; omega)
    _ ≤ ∑ d ∈ (Icc 1 M).filter Squarefree, cc d / (d : ℝ) ^ 2 *
          ∑ k ∈ (Icc 1 M).filter (fun k => X < d * k), 1 / (k : ℝ) ^ 2 := swap_le X M
    _ ≤ ∑ d ∈ (Icc 1 M).filter Squarefree, cc d / (d : ℝ) ^ 2 * (2 * d / ((X : ℝ) + 1)) := by
        refine sum_le_sum fun d hd => ?_
        have hd1 : 0 < d := (mem_Icc.mp (mem_filter.mp hd).1).1
        exact mul_le_mul_of_nonneg_left (sum_k_le X M d hd1)
          (div_nonneg (cc_nonneg d) (by positivity))
    _ = 2 / ((X : ℝ) + 1) * ∑ d ∈ (Icc 1 M).filter Squarefree, cc d / d := by
        rw [mul_sum]; refine sum_congr rfl fun d hd => ?_
        have hd1 : 0 < d := (mem_Icc.mp (mem_filter.mp hd).1).1
        have : (d : ℝ) ≠ 0 := by exact_mod_cast hd1.ne'
        field_simp
    _ ≤ 2 / ((X : ℝ) + 1) * Real.exp 4 :=
        mul_le_mul_of_nonneg_left (sum_cc_div_le M) (by positivity)
    _ = 2 * Real.exp 4 / ((X : ℝ) + 1) := by ring

set_option maxHeartbeats 800000 in
/-- **`|Σ_v h(v) - Σ_{v ≤ X} h(v)| ≤ 2e⁴/(X+1)`.** PROVED. -/
theorem tail_tsum (Z m X : ℕ) :
    ‖hsum Z m - ∑ v ∈ Icc 1 X, hv Z m v‖ ≤ 2 * Real.exp 4 / ((X : ℝ) + 1) := by
  have hs : Summable (fun v => hv Z m v) := (summable_norm_hv Z m).of_norm
  have hsplit := hs.sum_add_tsum_nat_add (X + 1)
  have hIcc : ∑ v ∈ Icc 1 X, hv Z m v = ∑ v ∈ range (X + 1), hv Z m v := by
    have e : Icc 1 X = Ico 1 (X + 1) := by ext; simp only [mem_Icc, mem_Ico]; omega
    rw [e, sum_Ico_eq_sub _ (by omega : 1 ≤ X + 1), sum_range_one, hv_zero, sub_zero]
  unfold hsum
  rw [hIcc, ← hsplit, add_sub_cancel_left]
  have hsn : Summable (fun i => ‖hv Z m (i + (X + 1))‖) :=
    (summable_nat_add_iff (X + 1)).mpr (summable_norm_hv Z m)
  refine le_trans (norm_tsum_le_tsum_norm hsn) ?_
  refine tsum_le_of_sum_le (fun i => norm_nonneg _) fun s => ?_
  have hmap : ∑ i ∈ s, ‖hv Z m (i + (X + 1))‖ =
      ∑ v ∈ s.map (addRightEmbedding (X + 1)), ‖hv Z m v‖ := by
    rw [sum_map]; rfl
  rw [hmap]
  refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _))
    (tail_hv Z m X (s.sup id + (X + 1)))
  intro v hv
  rw [Finset.mem_map] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  rw [mem_Ioc]
  have := le_sup (f := id) hi
  simp only [addRightEmbedding_apply, id] at this ⊢
  omega

/-! ### Step 4: a crude bound for `f(w)` -/

theorem abs_muphi_le (d : ℕ) : |muphi d| ≤ 1 := by
  unfold muphi
  rcases Nat.eq_zero_or_pos d.totient with h | h
  · rw [h]; simp
  · rw [abs_div, abs_of_pos (by exact_mod_cast h : (0 : ℝ) < d.totient)]
    have h1 : (1 : ℝ) ≤ d.totient := by exact_mod_cast h
    have h2 : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    exact le_trans (div_le_self (abs_nonneg _) h1) h2

theorem card_R0_le_q0 (Z : ℕ) : #(R0 Z) ≤ q0 Z := by
  calc #(R0 Z) ≤ #(Icc 1 (q0 Z)) := card_le_card (filter_subset _ _)
    _ = q0 Z := by simp

theorem norm_inner_le (Z w a : ℕ) : ‖MajorArcs.inner Z w a‖ ≤ (q0 Z : ℝ) * q0 Z := by
  unfold MajorArcs.inner
  calc _ ≤ ∑ ℓ ∈ range (q0 Z), ‖(muphi (qell Z w a ℓ) : ℂ) *
          ∑ r ∈ R0 Z, ee (-((ℓ : ℝ) * r / q0 Z))‖ := norm_sum_le _ _
    _ ≤ ∑ ℓ ∈ range (q0 Z), (q0 Z : ℝ) := by
        refine sum_le_sum fun ℓ _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h1 : ‖∑ r ∈ R0 Z, ee (-((ℓ : ℝ) * r / q0 Z))‖ ≤ q0 Z := by
          calc _ ≤ ∑ r ∈ R0 Z, ‖ee (-((ℓ : ℝ) * r / q0 Z))‖ := norm_sum_le _ _
            _ = #(R0 Z) := by simp [norm_ee]
            _ ≤ q0 Z := by exact_mod_cast card_R0_le_q0 Z
        calc |muphi (qell Z w a ℓ)| * ‖∑ r ∈ R0 Z, ee (-((ℓ : ℝ) * r / q0 Z))‖
            ≤ 1 * (q0 Z : ℝ) := mul_le_mul (abs_muphi_le _) h1 (norm_nonneg _) zero_le_one
          _ = q0 Z := one_mul _
    _ = (q0 Z : ℝ) * q0 Z := by simp

/-- **`|f(w)| ≤ q_0⁴`** for `w ≤ q_0`. -/
theorem norm_fq_le (Z m w : ℕ) (hw : w ≤ q0 Z) : ‖fq Z m w‖ ≤ (q0 Z : ℝ) ^ 4 := by
  unfold fq
  have hn : (0 : ℝ) < q0 Z := by exact_mod_cast q0_pos Z
  rw [norm_mul]
  have h1 : ‖(1 : ℂ) / (q0 Z : ℂ) ^ 3‖ = 1 / (q0 Z : ℝ) ^ 3 := by
    rw [norm_div, norm_one, norm_pow, Complex.norm_natCast]
  have hcard : #((Icc 1 w).filter (fun a => a.Coprime w)) ≤ q0 Z :=
    le_trans (card_le_card (filter_subset _ _)) (by simp; exact hw)
  have h2 : ‖∑ a ∈ (Icc 1 w).filter (fun a => a.Coprime w),
      ee (-((a : ℝ) * m / w)) * MajorArcs.inner Z w a ^ 3‖ ≤
      (q0 Z : ℝ) * ((q0 Z : ℝ) * q0 Z) ^ 3 := by
    calc _ ≤ ∑ a ∈ (Icc 1 w).filter (fun a => a.Coprime w),
          ‖ee (-((a : ℝ) * m / w)) * MajorArcs.inner Z w a ^ 3‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ (Icc 1 w).filter (fun a => a.Coprime w), ((q0 Z : ℝ) * q0 Z) ^ 3 := by
          refine sum_le_sum fun a _ => ?_
          rw [norm_mul, norm_ee, one_mul, norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le Z w a) 3
      _ = (#((Icc 1 w).filter (fun a => a.Coprime w)) : ℝ) * ((q0 Z : ℝ) * q0 Z) ^ 3 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (q0 Z : ℝ) * ((q0 Z : ℝ) * q0 Z) ^ 3 := by
          gcongr
  rw [h1]
  calc 1 / (q0 Z : ℝ) ^ 3 * ‖∑ a ∈ (Icc 1 w).filter (fun a => a.Coprime w),
        ee (-((a : ℝ) * m / w)) * MajorArcs.inner Z w a ^ 3‖
      ≤ 1 / (q0 Z : ℝ) ^ 3 * ((q0 Z : ℝ) * ((q0 Z : ℝ) * q0 Z) ^ 3) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (q0 Z : ℝ) ^ 4 := by field_simp

/-! ### Step 5: (7.2) and `Tail72` -/

/-- **`|Σ_{q ≤ N} f(q) - G(q_0) Σ_v h(v)| ≤ 2e⁴ q_0⁶/(N+1)`.** PROVED. -/
theorem sing_diff (Z m N : ℕ) :
    ‖∑ q ∈ Icc 1 N, fq Z m q - Gq0 Z m * hsum Z m‖ ≤
      (q0 Z : ℝ) ^ 6 * (2 * Real.exp 4) / ((N : ℝ) + 1) := by
  have hn : (0 : ℝ) < q0 Z := by exact_mod_cast q0_pos Z
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [sum_fq_split, Gq0, sum_mul, ← sum_sub_distrib]
  simp_rw [← mul_sub]
  have hterm : ∀ w ∈ (q0 Z).divisors,
      ‖fq Z m w * (∑ v ∈ Icc 1 (N / w), hv Z m v - hsum Z m)‖ ≤
        (q0 Z : ℝ) ^ 4 * (2 * Real.exp 4 * q0 Z / ((N : ℝ) + 1)) := by
    intro w hw
    have hw0 := Nat.pos_of_mem_divisors hw
    have hwn : w ≤ q0 Z := Nat.divisor_le hw
    rw [norm_mul, norm_sub_rev]
    refine mul_le_mul (norm_fq_le Z m w hwn) ?_ (norm_nonneg _) (by positivity)
    refine le_trans (tail_tsum Z m (N / w)) ?_
    have h1 : N + 1 ≤ (N / w + 1) * q0 Z := by
      have h := Nat.lt_div_mul_add (a := N) hw0
      have : N + 1 ≤ (N / w + 1) * w := by rw [add_mul, one_mul]; omega
      exact le_trans this (Nat.mul_le_mul_left _ hwn)
    have h1' : (N : ℝ) + 1 ≤ (((N / w : ℕ) : ℝ) + 1) * q0 Z := by exact_mod_cast h1
    rw [div_le_div_iff₀ (by positivity) hN]
    have he : 0 ≤ 2 * Real.exp 4 := by positivity
    nlinarith
  calc ‖∑ w ∈ (q0 Z).divisors, fq Z m w * (∑ v ∈ Icc 1 (N / w), hv Z m v - hsum Z m)‖
      ≤ ∑ w ∈ (q0 Z).divisors, ‖fq Z m w * (∑ v ∈ Icc 1 (N / w), hv Z m v - hsum Z m)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ w ∈ (q0 Z).divisors, (q0 Z : ℝ) ^ 4 * (2 * Real.exp 4 * q0 Z / ((N : ℝ) + 1)) :=
        sum_le_sum hterm
    _ = (#(q0 Z).divisors : ℝ) * ((q0 Z : ℝ) ^ 4 * (2 * Real.exp 4 * q0 Z / ((N : ℝ) + 1))) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (q0 Z : ℝ) * ((q0 Z : ℝ) ^ 4 * (2 * Real.exp 4 * q0 Z / ((N : ℝ) + 1))) := by
        gcongr; exact_mod_cast Nat.card_divisors_le_self _
    _ = (q0 Z : ℝ) ^ 6 * (2 * Real.exp 4) / ((N : ℝ) + 1) := by ring

/-- **`Tail72 A B` PROVED** for every `A` and `B`: display (7.2) with (7.3)-(7.15), with
`C = 2e⁴`, `u_0 = e`. Oddness of `m` and `4u ≤ m ≤ 5u` are not used. -/
theorem tail72 (A B : ℕ) : Tail72 A B := by
  refine ⟨2 * Real.exp 4, Real.exp 1, fun u hu m _ _ _ => ?_⟩
  have hL : 1 ≤ Real.log u := by
    have := Real.log_le_log (Real.exp_pos 1) hu
    rwa [Real.log_exp] at this
  have hL0 : 0 < Real.log u := by linarith
  have hd := sing_diff (Zof A u) m ⌊Real.log u ^ B⌋₊
  unfold SingP
  have hP : Real.log u ^ B < (⌊Real.log u ^ B⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hq := q0_sq_le A u hL
  have hn6 : (q0 (Zof A u) : ℝ) ^ 6 ≤ Real.log u ^ (27 * (A : ℝ)) := by
    have e : (q0 (Zof A u) : ℝ) ^ 6 = ((q0 (Zof A u) : ℝ) ^ 2) ^ 3 := by ring
    rw [e]
    calc ((q0 (Zof A u) : ℝ) ^ 2) ^ 3 ≤ (Real.log u ^ (9 * (A : ℝ))) ^ 3 :=
          pow_le_pow_left₀ (by positivity) hq 3
      _ = Real.log u ^ (27 * (A : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring
  have hLB : (0 : ℝ) < Real.log u ^ B := by positivity
  calc ‖∑ q ∈ Icc 1 ⌊Real.log u ^ B⌋₊, fq (Zof A u) m q - Gq0 (Zof A u) m * hsum (Zof A u) m‖
      ≤ (q0 (Zof A u) : ℝ) ^ 6 * (2 * Real.exp 4) / ((⌊Real.log u ^ B⌋₊ : ℝ) + 1) := hd
    _ ≤ Real.log u ^ (27 * (A : ℝ)) * (2 * Real.exp 4) / Real.log u ^ B :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hn6 (by positivity)) hLB hP.le
    _ = 2 * Real.exp 4 * Real.log u ^ (27 * (A : ℝ) - B) := by
        rw [Real.rpow_sub hL0, Real.rpow_natCast]; ring
    _ ≤ 2 * Real.exp 4 * Real.log u ^ (-((B : ℝ) - 27 * A - 1)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (by linarith))
          (by positivity)

/-- **MajorLower, CONDITIONAL ON `Major618 A B`** only. -/
theorem majorLower_of_618 (A B : ℕ) (hA : 1 ≤ A) (hB : 36 * A + 3 ≤ B)
    (h618 : Major618 A B) : MajorLower A B (9 * (A : ℝ) + 1) :=
  majorLower_of_analytic A B hA hB h618 (tail72 A B)

/-- **RepProp A, CONDITIONAL ON `Minor516W A B` and `Major618 A B`** only, the two
Siegel-Walfisz inputs, for `A ≥ 1`, `B ≥ 36A + 3`, `B ≥ 28A + 13`. -/
theorem repProp_of_two (A B : ℕ) (hA : 1 ≤ A) (hB1 : 36 * A + 3 ≤ B) (hB2 : 28 * A + 13 ≤ B)
    (hmin : RepAssembly.Minor516W A B) (h618 : Major618 A B) : RepProp A :=
  repProp_of_analytic A B hA hB1 hB2 hmin h618 (tail72 A B)

/-! ### Vacuity tests -/

/-- `fq_split` at `Z = 4`, `q_0 = 6`, `q = 12`: `w = 6`, `v = 2`, a genuine instance of the
non-coprime case, so `f(12) = f(6) h(2) = 0`. -/
example (m : ℕ) : fq 4 m 12 = fq 4 m (Nat.gcd 12 (q0 4)) * hv 4 m (12 / Nat.gcd 12 (q0 4)) :=
  fq_split 4 m 12 (by norm_num)

/-- `fq_mul` at `Z = 4`, `q_0 = 6`, `w = 3`, `v = 5`: the coprime case. -/
example (m : ℕ) : fq 4 m (3 * 5) = fq 4 m 3 * hv 4 m 5 := by
  have hq : q0 4 = 6 := by decide
  exact fq_mul 4 m 3 5 (by rw [hq]; norm_num) (by norm_num) (by norm_num) (by rw [hq]; norm_num)

/-- `tail_hv` with `X = 0` bounds the whole partial sum of `|h|` by `2e⁴`. -/
example (Z m M : ℕ) : ∑ v ∈ Ioc 0 M, ‖hv Z m v‖ ≤ 2 * Real.exp 4 := by
  have := tail_hv Z m 0 M; simpa using this

/-- The side conditions of `repProp_of_two` hold at `A = 1`, `B = 41`. -/
example : 1 ≤ (1 : ℕ) ∧ 36 * 1 + 3 ≤ (41 : ℕ) ∧ 28 * 1 + 13 ≤ (41 : ℕ) := by norm_num

end LeanLab.SparseTernary.Tail72Proof
