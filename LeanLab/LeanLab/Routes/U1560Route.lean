/-
U-1560, T3 MOONSHOT, route: the Kloosterman refined Farey dissection, the delta method
circle method of Kloosterman, Heath-Brown and Duke-Friedlander-Iwaniec, applied to the
binary Goldbach count.

The route puts every frequency k/M of an exact finite Fourier identity on the arc of its
reduced fraction a/q, keeps ALL denominators q up to about √M as major arcs, and asks for
cancellation over the numerators a inside each q, the Kloosterman refinement, instead of
absolute bounds arc by arc.

Smallest Lean lemma the route needs: the exact regrouping of the M-th roots of unity by
reduced fractions,
  ∑_{k < M} f(k/M) = ∑_{q ∣ M} ∑_{a < q, gcd(a, q) = 1} f(a/q),
`sum_range_eq_sum_reduced`, and its delta symbol corollary
  ∑_{q ∣ M} c_q(n) = M · [M ∣ n]  for the Ramanujan sums c_q,
`delta_ramanujan`. Both are KNOWN classical mathematics.

AI wrote this Lean code. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import Mathlib

open Finset Complex

namespace LeanLab.Routes.U1560

/-- The reduced fractions `a/q` with `q ∣ M` and `0 ≤ a < q`, `gcd(a, q) = 1`, as pairs `(q, a)`. -/
def reduced (M : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  M.divisors.sigma fun q => (range q).filter fun a => Nat.Coprime a q

lemma mem_reduced {M : ℕ} {x : Σ _ : ℕ, ℕ} :
    x ∈ reduced M ↔ x.1 ∣ M ∧ M ≠ 0 ∧ x.2 < x.1 ∧ Nat.Coprime x.2 x.1 := by
  simp [reduced, Finset.mem_sigma, Nat.mem_divisors, and_assoc]

/-- Regrouping the `M`-th roots of unity by reduced fractions: for any `f : ℚ → β`,
`∑_{k < M} f(k/M) = ∑_{q ∣ M} ∑_{a < q, (a, q) = 1} f(a/q)`. -/
theorem sum_range_eq_sum_reduced {β : Type*} [AddCommMonoid β] {M : ℕ} (hM : M ≠ 0)
    (f : ℚ → β) :
    ∑ k ∈ range M, f ((k : ℚ) / M) =
      ∑ q ∈ M.divisors, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), f ((a : ℚ) / q) := by
  rw [show (∑ q ∈ M.divisors, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      f ((a : ℚ) / q)) = ∑ x ∈ reduced M, f ((x.2 : ℚ) / x.1) from
      (Finset.sum_sigma _ _ (fun x : Σ _ : ℕ, ℕ => f ((x.2 : ℚ) / x.1))).symm]
  symm
  refine Finset.sum_bij' (fun x _ => x.2 * (M / x.1))
    (fun k _ => (⟨M / Nat.gcd k M, k / Nat.gcd k M⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_ ?_
  · -- maps into range M
    intro x hx
    obtain ⟨hq, -, ha, -⟩ := (mem_reduced).1 hx
    rw [Finset.mem_range]
    have hqpos : 0 < x.1 := Nat.pos_of_ne_zero (by rintro h; rw [h] at ha; omega)
    obtain ⟨d, hd⟩ := hq
    have hdpos : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hd; exact hM hd)
    rw [hd, Nat.mul_div_cancel_left _ hqpos]
    calc x.2 * d < x.1 * d := Nat.mul_lt_mul_of_pos_right ha hdpos
      _ = x.1 * d := rfl
  · -- maps into reduced M
    intro k hk
    rw [Finset.mem_range] at hk
    have hg : 0 < Nat.gcd k M := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hM)
    refine (mem_reduced).2 ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_right k M), hM, ?_, ?_⟩
    · exact Nat.div_lt_div_of_lt_of_dvd (Nat.gcd_dvd_right k M) hk
    · exact Nat.coprime_div_gcd_div_gcd hg
  · -- left inverse
    intro x hx
    obtain ⟨hq, -, ha, hcop⟩ := (mem_reduced).1 hx
    have hqpos : 0 < x.1 := Nat.pos_of_ne_zero (by rintro h; rw [h] at ha; omega)
    obtain ⟨d, hd⟩ := hq
    have hdpos : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hd; exact hM hd)
    have hMd : M / x.1 = d := by rw [hd, Nat.mul_div_cancel_left _ hqpos]
    rw [hMd]
    have hgcd : Nat.gcd (x.2 * d) M = d := by
      rw [hd, Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul]
    rw [hgcd, Nat.mul_div_cancel _ hdpos, hd, Nat.mul_div_cancel _ hdpos]
  · -- right inverse
    intro k hk
    have hg : 0 < Nat.gcd k M := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hM)
    simp only
    rw [Nat.div_div_self (Nat.gcd_dvd_right k M) hM]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left k M)
  · -- the values agree: (a·(M/q))/M = a/q
    intro x hx
    obtain ⟨hq, -, ha, -⟩ := (mem_reduced).1 hx
    have hqpos : 0 < x.1 := Nat.pos_of_ne_zero (by rintro h; rw [h] at ha; omega)
    obtain ⟨d, hd⟩ := hq
    have hdpos : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hd; exact hM hd)
    have hMd : M / x.1 = d := by rw [hd, Nat.mul_div_cancel_left _ hqpos]
    congr 1
    rw [hMd, hd]
    push_cast
    have : (d : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
    field_simp

/-- The additive character `e(x) = exp(2πi x)` on `ℚ`. -/
noncomputable def e (x : ℚ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

/-- The Ramanujan sum `c_q(n) = ∑_{a < q, (a, q) = 1} e(a n / q)`. -/
noncomputable def ramanujan (q n : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), e ((a : ℚ) / q * n)

lemma e_nat_div {M : ℕ} (k n : ℕ) :
    e ((k : ℚ) / M * n) = Complex.exp (2 * Real.pi * Complex.I / M) ^ (k * n) := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Orthogonality of the `M`-th roots of unity. -/
lemma sum_root_pow {M : ℕ} (hM : M ≠ 0) (m : ℕ) :
    ∑ k ∈ range M, Complex.exp (2 * Real.pi * Complex.I / M) ^ (k * m) =
      if M ∣ m then (M : ℂ) else 0 := by
  have hp : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / M)) M := by
    have := Complex.isPrimitiveRoot_exp M hM
    simpa [mul_div_assoc] using this
  set z := Complex.exp (2 * Real.pi * Complex.I / M)
  have hrw : ∀ k, z ^ (k * m) = (z ^ m) ^ k := fun k => by rw [← pow_mul, mul_comm]
  simp_rw [hrw]
  split_ifs with hd
  · have h1 : z ^ m = 1 := (hp.pow_eq_one_iff_dvd m).2 hd
    simp [h1]
  · have h1 : z ^ m ≠ 1 := fun h => hd ((hp.pow_eq_one_iff_dvd m).1 h)
    rw [geom_sum_eq h1]
    have h2 : (z ^ m) ^ M = 1 := by rw [← pow_mul, mul_comm, pow_mul, hp.pow_eq_one, one_pow]
    simp [h2]

/-- The delta symbol of the Kloosterman refinement in exact finite form:
`∑_{q ∣ M} c_q(n) = M · [M ∣ n]`. -/
theorem delta_ramanujan {M : ℕ} (hM : M ≠ 0) (n : ℕ) :
    ∑ q ∈ M.divisors, ramanujan q n = if M ∣ n then (M : ℂ) else 0 := by
  unfold ramanujan
  rw [← sum_range_eq_sum_reduced hM (fun x => e (x * n))]
  simp_rw [e_nat_div]
  exact sum_root_pow hM n

/-- Vacuity instance: for `M = 6`, the `6`-th roots regroup into `q ∈ {1, 2, 3, 6}`
with `1 + 1 + 2 + 2 = 6` reduced fractions. -/
example : (reduced 6).card = 6 := by decide

/-- Vacuity instance for the delta identity: `M = 6`, `n = 12`. -/
example : ∑ q ∈ (6 : ℕ).divisors, ramanujan q 12 = 6 := by
  rw [delta_ramanujan (by norm_num)]
  norm_num

end LeanLab.Routes.U1560

#print axioms LeanLab.Routes.U1560.sum_range_eq_sum_reduced
#print axioms LeanLab.Routes.U1560.delta_ramanujan
