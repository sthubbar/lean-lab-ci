import LeanLab.Halupczok2012.U1495PPS
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
Re-split of the Decomp398c input `PPS1984Uniform`, following the paper's own cut.
Source: Perelli, Pintz, Salerno, Bombieri's theorem in short intervals,
Ann. Sc. Norm. Sup. Pisa 11 (1984) 529 to 539, read from page images, copy papers/PPS1984.pdf.
https://www.numdam.org/item/ASNSP_1984_4_11_4_529_0/

Page 531 reduces the sum of `ppsTerm` over moduli to primitive characters, display 4,
cites Huxley Iwaniec for conductors below a power of x, display 5,
and leaves the dyadic primitive character sum, display 6, for pages 532 to 538.
The earlier split of Decomp398c cut the modulus range at x to the 1/100;
display 4 shows each large modulus still carries characters of small conductor,
so the cut here is on the conductor Q', as on page 531.

Plan: LeanLab/LeanLab/Halupczok2012/notes/burst-20261122/Halupczok2012-398c-resplit.md.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Resplit398c

open Finset
open scoped Classical ArithmeticFunction.vonMangoldt

/-- PPS1984 page 531, the quantity `E(z, h, χ)` under the first display:
the sum of `Λ(n) χ(n)` over `z < n ≤ z + h`, minus `h` when `χ` is principal.
For `z ≥ 0` the natural numbers `n` with `z < n ≤ z + h` are those in `Ioc ⌊z⌋ ⌊z + h⌋`. -/
noncomputable def charE {q : ℕ} (z h : ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ n ∈ Ioc ⌊z⌋₊ ⌊z + h⌋₊, (Λ n : ℂ) * χ n) - if χ = 1 then (h : ℂ) else 0

/-- PPS1984 page 531 display 6, left side: the sum over `Q'/2 < q ≤ Q'` and over primitive
characters `χ` mod `q` of `|E(z, h, χ)|`. The two maxima over `h ≤ y` and `x/2 < z ≤ x`
are encoded by arbitrary choice functions `h`, `z` of the character, as in `PPS1984Uniform`. -/
noncomputable def primSum (Q' : ℝ) (h z : (q : ℕ) → DirichletCharacter ℂ q → ℝ) : ℝ :=
  ∑ q ∈ (Icc 1 ⌊Q'⌋₊).filter (fun q : ℕ => Q' / 2 < (q : ℝ)),
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
      ‖charE (z q χ) (h q χ) χ‖

/-- LEAF: PPS1984 page 531 display 4, reduction to primitive characters.
Expand `ψ(z+h; q, a) - ψ(z; q, a) - h/φ(q)` by the first display of page 531,
replace each `χ` mod `q` by the primitive `χ₁` mod `q₁` inducing it at cost `≪ L²`,
sum `1/φ(q)` over the multiples `q` of `q₁` up to `Q`, which is `≪ log Q / φ(q₁)`,
and pass to the dyadic conductor block `Q'/2 < q ≤ Q'` giving the maximum.
The maximum over `Q' ≤ Q` and over `h, z` for each primitive character is encoded by
the existential `Q'`, `h'`, `z'`; with the implied constant `C` this is the printed display.
Class MEDIUM. No citation wall: the two auxiliary bounds are printed on page 531. -/
theorem display4_reduction :
    ∃ c : ℝ, 0 < c ∧ ∃ C x0 : ℝ, ∀ x y Q : ℝ, x0 ≤ x → 0 < y → y ≤ x → 1 ≤ Q → Q ≤ x →
      ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ), (∀ q, Int.gcd (a q) q = 1) →
      (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
      ∃ Q' : ℝ, 1 ≤ Q' ∧ Q' ≤ Q ∧ ∃ h' z' : (q : ℕ) → DirichletCharacter ℂ q → ℝ,
        (∀ q χ, 0 < h' q χ ∧ h' q χ ≤ y) ∧ (∀ q χ, x / 2 < z' q χ ∧ z' q χ ≤ x) ∧
        ∑ q ∈ Icc 1 ⌊Q⌋₊, ppsTerm (z q) (h q) q (a q) ≤
          C * (Real.log x ^ c / Q' * primSum Q' h' z') + C * Q * Real.log x ^ 3 := by
  sorry

/-- LEAF: PPS1984 page 531 display 5, the small conductors, with the Huxley Iwaniec range
of page 530, unnumbered display, third line, which at `θ` near 3/5 allows any conductor
exponent below 1/20; here `Q' ≤ x^(1/100)`. The paper proves nothing here and cites
Huxley Iwaniec, Mathematika 22 1975 pages 188 to 194, its reference 6.
Uniformity in `y` over `x^(3/5+ε) ≤ y ≤ x` is a reading of a fixed `θ` result,
the same caveat as `PPS1984Uniform`.
Class HARD. Citation wall: Huxley Iwaniec 1975, copy papers/HuxleyIwaniec1975.pdf. -/
theorem huxley_iwaniec_small_conductor :
    ∀ A c ε : ℝ, 0 < A → 0 < c → 0 < ε → ∃ C x0 : ℝ, ∀ x y Q' : ℝ,
      x0 ≤ x → x ^ (3 / 5 + ε) ≤ y → y ≤ x → 1 ≤ Q' → Q' ≤ x ^ (1 / 100 : ℝ) →
      ∀ h z : (q : ℕ) → DirichletCharacter ℂ q → ℝ,
      (∀ q χ, 0 < h q χ ∧ h q χ ≤ y) → (∀ q χ, x / 2 < z q χ ∧ z q χ ≤ x) →
      primSum Q' h z ≤ C * y * Q' * Real.log x ^ (-A - c) := by
  sorry

/-- LEAF: PPS1984 page 531 display 6, the dyadic primitive character sum for conductors
`x^(1/100) ≤ Q' ≤ y x^(-1/2) L^(-B)`, proved on pages 532 to 538 by the Heath Brown identity,
display 7 with `k = 4`, displays 8 to 11, Perron and the line shift, displays 12 to 16,
the Lemma with display 18, and Cases I and II with displays 19 to 24.
It can be split later at display 10, display 11, display 18 and the five cases.
Class HARD. Citation wall inside: the Lavrik approximate functional equation, reference 8,
used on page 536; no copy found. -/
theorem primitive_dyadic :
    ∀ A c ε : ℝ, 0 < A → 0 < c → 0 < ε → ∃ B : ℝ, 0 < B ∧ ∃ C x0 : ℝ, ∀ x y Q' : ℝ,
      x0 ≤ x → x ^ (3 / 5 + ε) ≤ y → y ≤ x → x ^ (1 / 100 : ℝ) ≤ Q' →
      Q' ≤ y * x ^ (-(1 / 2) : ℝ) * Real.log x ^ (-B) →
      ∀ h z : (q : ℕ) → DirichletCharacter ℂ q → ℝ,
      (∀ q χ, 0 < h q χ ∧ h q χ ≤ y) → (∀ q χ, x / 2 < z q χ ∧ z q χ ≤ x) →
      primSum Q' h z ≤ C * y * Q' * Real.log x ^ (-A - c) := by
  sorry

/-- `primSum` is a sum of norms. -/
lemma primSum_nonneg (Q' : ℝ) (h z : (q : ℕ) → DirichletCharacter ℂ q → ℝ) :
    0 ≤ primSum Q' h z :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _

/-- The conductor bound used on page 531 after display 6: displays 5 and 6 together bound
every dyadic block `1 ≤ Q' ≤ Q`, with one constant. -/
lemma all_conductors {A c ε : ℝ} (hA : 0 < A) (hc : 0 < c) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∃ K x0 : ℝ, 0 ≤ K ∧ ∀ x y Q' : ℝ,
      x0 ≤ x → x ^ (3 / 5 + ε) ≤ y → y ≤ x → 1 ≤ Q' →
      Q' ≤ y * x ^ (-(1 / 2) : ℝ) * Real.log x ^ (-B) →
      ∀ h z : (q : ℕ) → DirichletCharacter ℂ q → ℝ,
      (∀ q χ, 0 < h q χ ∧ h q χ ≤ y) → (∀ q χ, x / 2 < z q χ ∧ z q χ ≤ x) →
      primSum Q' h z ≤ K * y * Q' * Real.log x ^ (-A - c) := by
  obtain ⟨Cb, xb, hb⟩ := huxley_iwaniec_small_conductor A c ε hA hc hε
  obtain ⟨B, hB, Cc, xc, hcc⟩ := primitive_dyadic A c ε hA hc hε
  refine ⟨B, hB, max (max Cb Cc) 0, max (max xb xc) 1, le_max_right _ _, ?_⟩
  intro x y Q' hx hy1 hy2 hQ1 hQ2 h z hh hz
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hy0 : 0 ≤ y := (Real.rpow_nonneg (by linarith) _).trans hy1
  have hw : 0 ≤ y * Q' * Real.log x ^ (-A - c) :=
    mul_nonneg (mul_nonneg hy0 (by linarith)) (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  have key : ∀ K : ℝ, K ≤ max (max Cb Cc) 0 →
      K * y * Q' * Real.log x ^ (-A - c) ≤ max (max Cb Cc) 0 * y * Q' * Real.log x ^ (-A - c) := by
    intro K hK
    have := mul_le_mul_of_nonneg_right hK hw
    simpa only [mul_assoc] using this
  rcases le_or_gt Q' (x ^ (1 / 100 : ℝ)) with hs | hl
  · exact (hb x y Q' ((le_max_left _ _).trans ((le_max_left _ _).trans hx)) hy1 hy2 hQ1 hs
      h z hh hz).trans (key Cb ((le_max_left _ _).trans (le_max_left _ _)))
  · exact (hcc x y Q' ((le_max_right _ _).trans ((le_max_left _ _).trans hx)) hy1 hy2 hl.le hQ2
      h z hh hz).trans (key Cc ((le_max_right _ _).trans (le_max_left _ _)))

/-- PPS1984 page 531, displays 4, 5 and 6 give the uniform theorem `PPS1984Uniform`,
the input of Decomp398c. The term `Q L³` of display 4 is absorbed since
`Q ≤ y x^(-1/2) L^(-B)` and `L^(3 - B + A) ≤ x^(1/2)` for large `x`. -/
theorem pps_uniform_of_leaves : PPS1984Uniform := by
  intro A ε hA hε
  obtain ⟨c, hc, Ca, xa, ha⟩ := display4_reduction
  obtain ⟨B, hB, K, xk, hK0, hK⟩ := all_conductors hA hc hε
  obtain ⟨x1, hx1⟩ := eventually_log_rpow_le (3 - B + A) (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨B, hB, max Ca 0 * K + max Ca 0, max (max xa xk) (max x1 3), ?_⟩
  intro x y Q hx hy1 hy2 hQ a h z hag hh hz
  have hxa : xa ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxk : xk ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx1' : x1 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hx3 : 3 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hxpos : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := one_le_log_of_three_le hx3
  have hLpos : 0 < Real.log x := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos _) hy1
  have hCa : 0 ≤ max Ca 0 := le_max_right _ _
  have hLA : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hLpos.le _
  have hRHS : 0 ≤ (max Ca 0 * K + max Ca 0) * y * Real.log x ^ (-A) :=
    mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg hCa hK0) hCa) hy0.le) hLA
  rcases lt_or_ge Q 1 with hQ1 | hQ1
  · have he : Icc 1 ⌊Q⌋₊ = ∅ := by
      rw [Finset.Icc_eq_empty_iff, not_le]
      have : ⌊Q⌋₊ = 0 := Nat.floor_eq_zero.mpr hQ1
      omega
    rw [he, sum_empty]
    exact hRHS
  -- `Q ≤ x`, since `x^(-1/2) ≤ 1` and `L^(-B) ≤ 1`.
  have hxh : x ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hLB : Real.log x ^ (-B) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hQx : Q ≤ x := by
    calc Q ≤ y * x ^ (-(1 / 2) : ℝ) * Real.log x ^ (-B) := hQ
      _ ≤ y * 1 * 1 := by
          gcongr
      _ ≤ x := by linarith
  obtain ⟨Q', hQ'1, hQ'Q, h', z', hh', hz', hred⟩ :=
    ha x y Q hxa hy0 hy2 hQ1 hQx a h z hag hh hz
  have hprim := hK x y Q' hxk hy1 hy2 hQ'1 (hQ'Q.trans hQ) h' z' hh' hz'
  -- display 6 inserted in display 4
  have hmain : Real.log x ^ c / Q' * primSum Q' h' z' ≤ K * y * Real.log x ^ (-A) := by
    have hQ'pos : 0 < Q' := by linarith
    have hLc : 0 ≤ Real.log x ^ c / Q' := div_nonneg (Real.rpow_nonneg hLpos.le _) hQ'pos.le
    calc Real.log x ^ c / Q' * primSum Q' h' z'
        ≤ Real.log x ^ c / Q' * (K * y * Q' * Real.log x ^ (-A - c)) :=
          mul_le_mul_of_nonneg_left hprim hLc
      _ = K * y * (Real.log x ^ c * Real.log x ^ (-A - c)) * (Q' / Q') := by ring
      _ = K * y * Real.log x ^ (-A) := by
          rw [← Real.rpow_add hLpos, div_self hQ'pos.ne']
          ring_nf
  -- the term `Q L³`
  have htail : Q * Real.log x ^ 3 ≤ y * Real.log x ^ (-A) := by
    have hD := hx1 x hx1'
    have hL3 : Real.log x ^ (3 : ℕ) = Real.log x ^ (3 : ℝ) := (Real.rpow_natCast _ 3).symm
    have hxx : x ^ (-(1 / 2) : ℝ) * x ^ (1 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add hxpos]; norm_num
    have hsplit : Real.log x ^ (-B) * Real.log x ^ (3 : ℝ) =
        Real.log x ^ (3 - B + A) * Real.log x ^ (-A) := by
      rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos]; ring_nf
    calc Q * Real.log x ^ 3
        ≤ y * x ^ (-(1 / 2) : ℝ) * Real.log x ^ (-B) * Real.log x ^ 3 :=
          mul_le_mul_of_nonneg_right hQ (by positivity)
      _ = y * x ^ (-(1 / 2) : ℝ) * Real.log x ^ (3 - B + A) * Real.log x ^ (-A) := by
          rw [hL3, mul_assoc, hsplit]; ring
      _ ≤ y * x ^ (-(1 / 2) : ℝ) * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
          gcongr
      _ = y * Real.log x ^ (-A) := by rw [mul_assoc y, hxx, mul_one]
  have hred' : ∑ q ∈ Icc 1 ⌊Q⌋₊, ppsTerm (z q) (h q) q (a q) ≤
      max Ca 0 * (Real.log x ^ c / Q' * primSum Q' h' z') + max Ca 0 * Q * Real.log x ^ 3 := by
    rcases le_or_gt 0 Ca with hC | hC
    · rw [max_eq_left hC]; exact hred
    · rw [max_eq_right hC.le]
      have h1 : 0 ≤ Real.log x ^ c / Q' * primSum Q' h' z' :=
        mul_nonneg (div_nonneg (Real.rpow_nonneg hLpos.le _) (by linarith)) (primSum_nonneg _ _ _)
      have h2 : 0 ≤ Q * Real.log x ^ 3 := by positivity
      nlinarith
  calc _ ≤ max Ca 0 * (Real.log x ^ c / Q' * primSum Q' h' z') + max Ca 0 * Q * Real.log x ^ 3 :=
        hred'
    _ ≤ max Ca 0 * (K * y * Real.log x ^ (-A)) + max Ca 0 * (y * Real.log x ^ (-A)) := by
        rw [mul_assoc (max Ca 0) Q]
        exact add_le_add (mul_le_mul_of_nonneg_left hmain hCa) (mul_le_mul_of_nonneg_left htail hCa)
    _ = (max Ca 0 * K + max Ca 0) * y * Real.log x ^ (-A) := by ring

end LeanLab.Halupczok2012.Resplit398c
