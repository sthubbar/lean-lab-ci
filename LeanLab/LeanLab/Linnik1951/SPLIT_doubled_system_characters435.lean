/-
Split of the character orthogonality chain of the local doubled system expansion.
The target statement stays exactly as it is; this file adds four leaves and one
assembly that proves it from them without using it.

The argument, from pages 155, 159, 160 and 166 of the scan. The square integral of the
doubled prime system over the arc system clipped to the unit interval is rewritten as an
integral over the radius interval of the shifted squares at the reduced residues: the
system is the finitely many doubled rational intervals of denominator q, so a nonnegative
continuous function integrates over it at most as its shifted sum (two purely geometric
leaves). The shifted sum is then bounded pointwise, for every z, by the finite unit
character calculation: orthogonality of the unit group turns the sum over the reduced
residues into the principal square plus q times the nonprincipal squares, divided by the
totient, and the primes dividing q contribute a totient-sized square of the logarithm of
q. Integrating that pointwise bound over the radius interval gives the principal integral
and q times the nonprincipal integrals with a totient-sized log q error. The fourth leaf
is the step that removes the factor q from the nonprincipal mass and turns the log q error
into the sixth power of the logarithm of N with a factor two over tau: it is the only
step here that the shape of the statement needs and that the pointwise bound does not
supply, and it is stated on the integrals so that it can be checked on its own.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_doubled_system_expansion435

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. The covering step of the geometry. For q at least two and tau at least four,
every point of the arc system of denominator q that lies in the unit interval lies in one
of the doubled rational intervals of radius two over q tau about a reduced residue below
q. Only rational arithmetic and the positivity of q and tau are used; no integration, no
character and no bound on the prime system occurs. -/
theorem rational_cover435 (q : ℕ) [NeZero q] (τ : ℝ) (hq : 2 ≤ q) (hτ : 4 ≤ τ) :
    arcSystem111 q τ ∩ Set.Icc 0 1 ⊆
      ⋃ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Set.Icc ((a : ℝ) / q - 2 / ((q : ℝ) * τ)) ((a : ℝ) / q + 2 / ((q : ℝ) * τ)) := by
  sorry

/-- LEAF. The integral step of the geometry. For a nonnegative continuous function and a
cover of the clipped arc system by the doubled intervals of the reduced residues, the
integral over the clipped system is at most the integral over the radius interval of the
sum of the shifted values at the reduced residues. This is subadditivity of the integral
over a finite union together with translation of the interval, so it uses no property of
the function beyond nonnegativity and continuity, and none of the characters. The radius
is positive because tau is at least four. -/
theorem rational_cover_integral435 (q : ℕ) [NeZero q] (τ : ℝ) (f : ℝ → ℝ)
    (hτ : 4 ≤ τ) (hf : Continuous f) (hn : ∀ x : ℝ, 0 ≤ f x)
    (hcover : arcSystem111 q τ ∩ Set.Icc 0 1 ⊆
      ⋃ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Set.Icc ((a : ℝ) / q - 2 / ((q : ℝ) * τ))
          ((a : ℝ) / q + 2 / ((q : ℝ) * τ))) :
    (∫ α in arcSystem111 q τ ∩ Set.Icc 0 1, f α) ≤
      ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), f ((a : ℝ) / q + z) := by
  sorry

/-- LEAF. The finite unit character step, pointwise in z. At any z the sum of the squares
of the prime system shifted to the reduced residues below q is at most a constant over the
totient of q times the principal square plus q times the sum of the nonprincipal squares,
plus a constant times the totient of q times the square of the logarithm of q. The
orthogonality of the unit group gives the coefficient one over the totient, the Gauss
squares are bounded by q, and the primes dividing q are absorbed in the logarithmic term,
which is the count of distinct prime divisors of q squared. No tau, no integration and no
growth hypothesis occurs. -/
theorem rational_pointwise_characters435 :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q], 1 ≤ N → 2 ≤ q → ∀ z : ℝ,
      (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      B / (q.totient : ℝ) *
        (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
          (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖characterPrime280 χ N z‖ ^ 2) +
        B * (q.totient : ℝ) * Real.log q ^ 2 := by
  sorry

/-- LEAF. The step that removes the factor q from the nonprincipal mass and the square of
the logarithm of q from the error. For every modulus and every tau at least four, the
q-weighted nonprincipal square mass plus the totient of q squared over q tau times the
square of the logarithm of q is at most a constant at least one times the unweighted
nonprincipal mass plus a constant times the totient of q over tau times the sixth power of
the logarithm of N. This is the only step whose constant has to carry the size of q
against N; the three supplies above are uniform in q. -/
theorem local_error_absorption435 :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N q : ℕ) [NeZero q] (τ : ℝ), 1 ≤ N → 2 ≤ q → 4 ≤ τ →
      (q : ℝ) *
          (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
              ‖characterPrime280 χ N z‖ ^ 2) +
        (q.totient : ℝ) ^ 2 * (4 / ((q : ℝ) * τ)) * Real.log q ^ 2 ≤
      C *
          (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
              ‖characterPrime280 χ N z‖ ^ 2) +
        C * (q.totient : ℝ) * (2 / τ) * Real.log N ^ 6 := by
  sorry

/-- The real bookkeeping of the split. With the nonprincipal mass S, the principal mass A,
the logarithm-of-q error M and the logarithm-of-N error L, the q-weighted and totient-sized
left side is dominated by the constant-weighted principal and nonprincipal masses and the
constant times two over tau times L, provided the removal step already holds. -/
private theorem absorb435 {B C φ q τ A S M L : ℝ}
    (hB : 0 < B) (hC1 : 1 ≤ C) (hφ : 0 < φ) (hA : 0 ≤ A)
    (hstep : q * S + φ ^ 2 * (4 / (q * τ)) * M ≤ C * S + C * φ * (2 / τ) * L) :
    B / φ * (A + q * S) + B * φ * (4 / (q * τ)) * M ≤
      (B * C) / φ * (A + S) + (B * C) * (2 / τ) * L := by
  have hBφ : (0 : ℝ) ≤ B / φ := by positivity
  have hm := mul_le_mul_of_nonneg_left hstep hBφ
  have e1 : B / φ * (q * S + φ ^ 2 * (4 / (q * τ)) * M) =
      B / φ * (q * S) + B * φ * (4 / (q * τ)) * M := by
    field_simp
  have e2 : B / φ * (C * S + C * φ * (2 / τ) * L) =
      B * C / φ * S + B * C * (2 / τ) * L := by
    field_simp
  rw [e1, e2] at hm
  have hA' : B / φ * A ≤ B * C / φ * A := by
    apply mul_le_mul_of_nonneg_right _ hA
    apply div_le_div_of_nonneg_right _ hφ.le
    nlinarith [hB.le, hC1]
  have g1 : B / φ * (A + q * S) = B / φ * A + B / φ * (q * S) := by ring
  have g2 : B * C / φ * (A + S) = B * C / φ * A + B * C / φ * S := by ring
  rw [g1, g2]
  linarith [hm, hA']

/-- The character chain of the doubled system. The target statement is unchanged, proved
from the four supplies above without using the target theorem. -/
theorem doubled_system_characters435_split :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q] (τ : ℝ), 1 ≤ N → 2 ≤ q → 4 ≤ τ →
      (∫ α in arcSystem111 q τ ∩ Set.Icc 0 1, ‖primeFourier111 N α‖ ^ 2) ≤
        B / (q.totient : ℝ) *
          ((∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
              ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
            (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
                ‖characterPrime280 χ N z‖ ^ 2)) +
        B * (2 / τ) * Real.log N ^ 6 := by
  classical
  obtain ⟨B, hB, hb⟩ := rational_pointwise_characters435
  obtain ⟨C, hC1, hC⟩ := local_error_absorption435
  refine ⟨B * C, by positivity, ?_⟩
  intro N q _ τ hN hq hτ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hτpos : (0 : ℝ) < τ := by linarith
  have hφ : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hL : (0 : ℝ) ≤ Real.log N ^ 6 := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg h1
    positivity
  have hM : (0 : ℝ) ≤ Real.log q ^ 2 := sq_nonneg _
  set r : ℝ := 2 / ((q : ℝ) * τ) with hrdef
  have hr : 0 < r := by
    rw [hrdef]
    exact div_pos (by norm_num) (mul_pos (by linarith) hτpos)
  let F : Finset (DirichletCharacter ℂ q) := Finset.univ.filter (fun χ => χ ≠ 1)
  let J : ℝ → ℝ := fun z => ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
    (q : ℝ) * ∑ χ ∈ F, ‖characterPrime280 χ N z‖ ^ 2
  have hp : Continuous (fun z : ℝ =>
      ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) :=
    (continuous_character_prime357 (1 : DirichletCharacter ℂ q) N hN).norm.pow 2
  have hc (χ : DirichletCharacter ℂ q) :
      Continuous (fun z : ℝ => ‖characterPrime280 χ N z‖ ^ 2) :=
    (continuous_character_prime357 χ N hN).norm.pow 2
  have hJ : Continuous J := hp.add ((continuous_finset_sum F (fun χ _ => hc χ)).const_mul _)
  have hS : Continuous (fun z => ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) :=
    continuous_finset_sum _ (fun a _ =>
      ((continuous_prime_fourier111 N hN).norm.pow 2).comp
        (continuous_const.add continuous_id))
  have hgeo := rational_cover_integral435 q τ (fun α => ‖primeFourier111 N α‖ ^ 2) hτ
    ((continuous_prime_fourier111 N hN).norm.pow 2) (fun α => sq_nonneg _)
    (rational_cover435 q τ hq hτ)
  have hmono : (∫ z in -r..r, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      ∫ z in -r..r, B / (q.totient : ℝ) * J z +
        B * (q.totient : ℝ) * Real.log q ^ 2 :=
    intervalIntegral.integral_mono_on (by linarith) (hS.intervalIntegrable _ _)
      (((hJ.const_mul _).add continuous_const).intervalIntegrable _ _)
      (fun z _ => hb N q hN hq z)
  have hsplit : (∫ z in -r..r, J z) =
      (∫ z in -r..r, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
        (q : ℝ) * ∑ χ ∈ F, ∫ z in -r..r, ‖characterPrime280 χ N z‖ ^ 2 := by
    dsimp [J]
    rw [intervalIntegral.integral_add (hp.intervalIntegrable _ _)
      (((continuous_finset_sum F (fun χ _ => hc χ)).const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finset_sum (fun χ _ => (hc χ).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_add ((hJ.const_mul _).intervalIntegrable _ _)
      intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hr2 : r - -r = 4 / ((q : ℝ) * τ) := by
    rw [hrdef]
    field_simp
    ring
  have hA0 : (0 : ℝ) ≤
      ∫ z in -r..r, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall (by linarith) (fun z => sq_nonneg _)
  have hconst : (r - -r) * (B * (q.totient : ℝ) * Real.log q ^ 2) =
      B * (q.totient : ℝ) * (4 / ((q : ℝ) * τ)) * Real.log q ^ 2 := by
    rw [hr2]
    ring
  rw [hsplit, hconst] at hmono
  exact hgeo.trans (hmono.trans (absorb435 hB hC1 hφ hA0 (hC N q τ hN hq hτ)))

end LeanLab.Linnik1951
