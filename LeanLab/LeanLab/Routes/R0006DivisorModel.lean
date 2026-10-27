import Mathlib

/-!
# R-0006, the binary additive divisor problem as a model of Goldbach

T3 MOONSHOT route, unit U-1030. AI wrote this Lean code. KNOWN mathematics.

`Σ_{a+b=N} d(a) d(b)` counts the lattice points `(x, y, u, v)` with `xy + uv = N`, all
positive: the divisor function is a convolution of `1` with itself, so the binary sum is a
quadratic form problem, which is why Estermann, Heath-Brown and Motohashi get it for EVERY `N`
through Kloosterman sums and spectral theory. `Λ` has no such factorization into smooth pieces;
that missing structure is the parity problem. This file proves the lattice-point identity.
-/

namespace LeanLab.Routes.R0006

open Finset

theorem card_antidiag (n : ℕ) : (Nat.divisorsAntidiagonal n).card = (Nat.divisors n).card := by
  rw [← Nat.map_div_right_divisors, card_map]

/-- the quadruples `((x, y), (u, v))` with `x y + u v = N`, grouped by `a = x y` -/
def quads (N : ℕ) : Finset (Σ _ : ℕ, (ℕ × ℕ) × (ℕ × ℕ)) :=
  (range (N + 1)).sigma (fun a => Nat.divisorsAntidiagonal a ×ˢ Nat.divisorsAntidiagonal (N - a))

/-- `Σ_{a ≤ N} d(a) d(N - a) = #quads N`, with `d(0) = 0` by Mathlib's convention -/
theorem card_quads (N : ℕ) :
    (quads N).card = ∑ a ∈ range (N + 1), (Nat.divisors a).card * (Nat.divisors (N - a)).card := by
  unfold quads
  rw [card_sigma]
  refine sum_congr rfl (fun a _ => ?_)
  rw [card_product, card_antidiag, card_antidiag]

/-- every quadruple solves `x y + u v = N` with all four entries positive -/
theorem mem_quads {N : ℕ} {q : Σ _ : ℕ, (ℕ × ℕ) × (ℕ × ℕ)} (h : q ∈ quads N) :
    q.2.1.1 * q.2.1.2 + q.2.2.1 * q.2.2.2 = N ∧
      0 < q.2.1.1 ∧ 0 < q.2.1.2 ∧ 0 < q.2.2.1 ∧ 0 < q.2.2.2 := by
  obtain ⟨a, ⟨x, y⟩, ⟨u, v⟩⟩ := q
  simp only [quads, mem_sigma, mem_range, mem_product, Nat.mem_divisorsAntidiagonal] at h
  obtain ⟨ha, ⟨hxy, ha0⟩, ⟨huv, hb0⟩⟩ := h
  refine ⟨by simp only; omega, ?_, ?_, ?_, ?_⟩ <;> simp only
  · exact Nat.pos_of_ne_zero (by rintro rfl; simp at hxy; omega)
  · exact Nat.pos_of_ne_zero (by rintro rfl; simp at hxy; omega)
  · exact Nat.pos_of_ne_zero (by rintro rfl; simp at huv; omega)
  · exact Nat.pos_of_ne_zero (by rintro rfl; simp at huv; omega)

/-- the lattice count: positive `(x, y, u, v)` in `[1, N]⁴` with `x y + u v = N` -/
def lattice (N : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((Icc 1 N ×ˢ Icc 1 N) ×ˢ (Icc 1 N ×ˢ Icc 1 N)).filter
    (fun p => p.1.1 * p.1.2 + p.2.1 * p.2.2 = N)

/-- **The binary additive divisor sum is a lattice point count.** PROVED. -/
theorem divisorSum_eq_lattice (N : ℕ) :
    ∑ a ∈ range (N + 1), (Nat.divisors a).card * (Nat.divisors (N - a)).card =
      (lattice N).card := by
  rw [← card_quads]
  refine card_bij (fun q _ => q.2) ?_ ?_ ?_
  · intro q hq
    obtain ⟨he, hx, hy, hu, hv⟩ := mem_quads hq
    simp only [lattice, mem_filter, mem_product, mem_Icc]
    refine ⟨⟨⟨⟨hx, ?_⟩, ⟨hy, ?_⟩⟩, ⟨⟨hu, ?_⟩, ⟨hv, ?_⟩⟩⟩, he⟩
    · nlinarith
    · nlinarith
    · nlinarith
    · nlinarith
  · intro q₁ hq₁ q₂ hq₂ h
    obtain ⟨a₁, p₁⟩ := q₁
    obtain ⟨a₂, p₂⟩ := q₂
    simp only at h
    subst h
    simp only [quads, mem_sigma, mem_range, mem_product, Nat.mem_divisorsAntidiagonal] at hq₁ hq₂
    have : a₁ = a₂ := by rw [← hq₁.2.1.1, ← hq₂.2.1.1]
    subst this; rfl
  · intro p hp
    simp only [lattice, mem_filter, mem_product, mem_Icc] at hp
    obtain ⟨⟨⟨⟨hx, -⟩, ⟨hy, -⟩⟩, ⟨⟨hu, -⟩, ⟨hv, -⟩⟩⟩, he⟩ := hp
    refine ⟨⟨p.1.1 * p.1.2, p⟩, ?_, rfl⟩
    simp only [quads, mem_sigma, mem_range, mem_product, Nat.mem_divisorsAntidiagonal]
    have h1 : 0 < p.1.1 * p.1.2 := Nat.mul_pos hx hy
    have h2 : 0 < p.2.1 * p.2.2 := Nat.mul_pos hu hv
    refine ⟨by omega, ?_, ?_⟩
    · simp only [true_and]; omega
    · constructor <;> omega

/-- vacuity check: `N = 4`, `d(1)d(3) + d(2)d(2) + d(3)d(1) = 2 + 4 + 2 = 8` lattice points -/
example : (lattice 4).card = 8 := by decide

end LeanLab.Routes.R0006
