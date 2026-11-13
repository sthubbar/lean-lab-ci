/-
P0093 pages 155, 156, 160 and 166. Character algebra and rational interval integration.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp376c
import LeanLab.Linnik1951.SPLIT1622_mellin
import LeanLab.Linnik1951.Principal442
import LeanLab.Linnik1951.FiniteCover435
import LeanLab.Linnik1951.SPLIT_rational_pointwise_characters442

namespace LeanLab.Linnik1951

open MeasureTheory Finset

/-- LEAF. P0093 page 155 equation 2.3 and page 160 orthogonality
before equation 5.4, applied to a square norm. Character expansion
and finite unit orthogonality bound the sum of shifted prime squares.
The principal Gauss square is at most one. The other Gauss squares
are at most q. There is no integration, tau or GRH. -/
theorem rational_pointwise_characters442 :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q], 1 ≤ N → 2 ≤ q → ∀ z : ℝ,
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      B / (q.totient : ℝ) *
        (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
          (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖characterPrime280 χ N z‖ ^ 2) +
        B * (q.totient : ℝ) * Real.log q ^ 2 := by
  exact rational_pointwise_characters442_split

/-- LEAF. P0093 page 166 definition of F_q as phi q doubled
intervals. For q at least two and tau at least four, integrate a
nonnegative continuous function on that system clipped to the unit
interval by shifting its finitely many reduced residue intervals.
This is rational geometry and integral translation only. -/
theorem rational_system_integral442 (q : ℕ) [NeZero q] (τ : ℝ)
    (hq : 2 ≤ q) (hτ : 4 ≤ τ) (f : ℝ → ℝ) (hf : Continuous f)
    (hn : ∀ x : ℝ, 0 ≤ f x) :
    (∫ α in arcSystem111 q τ ∩ Set.Icc 0 1, f α) ≤
      ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), f ((a : ℝ) / q + z) := by
  classical
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hτp : 0 < τ := by linarith
  let δ : ℝ := 2 / ((q : ℝ) * τ)
  have hδp : 0 < δ := by positivity
  have hδq : δ * (q : ℝ) ≤ 1 / 2 := by
    have he : δ * (q : ℝ) = 2 / τ := by dsimp [δ]; field_simp
    rw [he]
    apply (div_le_iff₀ hτp).mpr
    linarith
  let S : Finset ℕ := (range q).filter (fun a => Nat.Coprime a q)
  let I : ℕ → Set ℝ := fun a => Set.Icc ((a : ℝ) / q - δ) ((a : ℝ) / q + δ)
  have hcover : arcSystem111 q τ ∩ Set.Icc 0 1 ⊆ ⋃ a ∈ S, I a := by
    intro x hx
    obtain ⟨r, hrq, hrx⟩ := hx.1
    have hcast : (r : ℝ) = (r.num : ℝ) / (q : ℝ) := by rw [Rat.cast_def, hrq]
    have hnum : (r : ℝ) * (q : ℝ) = r.num := by rw [hcast]; field_simp
    change |x - (r : ℝ)| ≤ δ at hrx
    have hab := abs_le.mp hrx
    have hlo : -(δ : ℝ) ≤ (r : ℝ) := by change -δ ≤ (r : ℝ); linarith [hx.2.1]
    have hhi : (r : ℝ) ≤ 1 + δ := by change (r : ℝ) ≤ 1 + δ; linarith [hx.2.2]
    have hnlo : (-1 : ℝ) < (r.num : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right hlo hqp.le
      nlinarith
    have hnhi : (r.num : ℝ) < (q : ℝ) + 1 := by
      have hh := mul_le_mul_of_nonneg_right hhi hqp.le
      nlinarith
    have hnloZ : (-1 : ℤ) < r.num := by exact_mod_cast hnlo
    have hnhiZ : r.num < (q : ℤ) + 1 := by exact_mod_cast hnhi
    have hn0 : 0 ≤ r.num := by omega
    let a := r.num.toNat
    have hae : (a : ℤ) = r.num := Int.toNat_of_nonneg hn0
    have haR : (a : ℝ) = (r.num : ℝ) := by exact_mod_cast hae
    have hared : a.Coprime q := by
      have hh := r.reduced
      rw [hrq, ← hae] at hh
      simpa only [Int.natAbs_natCast] using hh
    have hale : a ≤ q := by omega
    have halt : a < q := by
      by_contra hn
      have he : a = q := by omega
      rw [he] at hared
      have hh : q = 1 := by simpa [Nat.Coprime] using hared
      omega
    have haS : a ∈ S := mem_filter.mpr ⟨mem_range.mpr halt, hared⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨a, haS, ?_⟩
    change (a : ℝ) / q - δ ≤ x ∧ x ≤ (a : ℝ) / q + δ
    rw [← haR] at hcast
    rw [hcast] at hab
    constructor <;> linarith [hab.1, hab.2]
  have hb := finite_cover_integral_indexed435 f hn (arcSystem111 q τ ∩ Set.Icc 0 1)
    S I (fun a _ => hf.integrableOn_Icc) hcover
  calc
    _ ≤ ∑ a ∈ S, ∫ α in I a, f α := hb
    _ = ∑ a ∈ S, ∫ z in -δ..δ, f ((a : ℝ) / q + z) := by
      apply Finset.sum_congr rfl
      intro a ha
      dsimp [I]
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
      rw [intervalIntegral.integral_comp_add_left]
      congr 1 <;> ring
    _ = _ := by
      exact (intervalIntegral.integral_finset_sum
        (fun a _ => (hf.comp (continuous_const.add continuous_id)).intervalIntegrable (-δ) δ)).symm

/-- P0093 pages 155, 160 and 166. Exact doubled_system_characters1622
statement from the pointwise finite character bound and the rational
interval integration step. Both smaller inputs now have clean proofs. -/
theorem doubled_system_characters_decomposed442 :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q] (τ : ℝ), 1 ≤ N → 2 ≤ q → 4 ≤ τ →
      (∫ α in arcSystem111 q τ ∩ Set.Icc 0 1, ‖primeFourier111 N α‖ ^ 2) ≤
        B / (q.totient : ℝ) *
          ((∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
              ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
                ‖characterPrime280 χ N z‖ ^ 2) +
        B * (q.totient : ℝ) * (2 / ((q : ℝ) * τ)) * Real.log q ^ 2 := by
  classical
  obtain ⟨B, hB, hb⟩ := rational_pointwise_characters442
  refine ⟨2 * B, by positivity, ?_⟩
  intro N q _ τ hN hq hτ
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hτp : 0 < τ := by linarith
  set r := 2 / ((q : ℝ) * τ) with hrdef
  have hr : 0 < r := by positivity
  let F : Finset (DirichletCharacter ℂ q) := univ.filter (fun χ => χ ≠ 1)
  let J : ℝ → ℝ := fun z => ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
    (q : ℝ) * ∑ χ ∈ F, ‖characterPrime280 χ N z‖ ^ 2
  have hp : Continuous (fun z : ℝ => ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) :=
    (continuous_character_prime357 (1 : DirichletCharacter ℂ q) N hN).norm.pow 2
  have hc (χ : DirichletCharacter ℂ q) : Continuous (fun z : ℝ => ‖characterPrime280 χ N z‖ ^ 2) :=
    (continuous_character_prime357 χ N hN).norm.pow 2
  have hJ : Continuous J := hp.add ((continuous_finset_sum F (fun χ _ => hc χ)).const_mul _)
  have hJ0 : ∀ z, 0 ≤ J z := by intro z; dsimp [J]; positivity
  have hS : Continuous (fun z => ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) :=
    continuous_finset_sum _ (fun a _ =>
      ((continuous_prime_fourier111 N hN).norm.pow 2).comp (continuous_const.add continuous_id))
  have hgeo := rational_system_integral442 q τ hq hτ
    (fun α => ‖primeFourier111 N α‖ ^ 2) ((continuous_prime_fourier111 N hN).norm.pow 2)
    (fun α => sq_nonneg _)
  have hmono : (∫ z in -r..r, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      ∫ z in -r..r, B / (q.totient : ℝ) * J z + B * (q.totient : ℝ) * Real.log q ^ 2 :=
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
  have hpos : 0 ≤ B / (q.totient : ℝ) * (∫ z in -r..r, J z) :=
    mul_nonneg (div_nonneg hB.le (Nat.cast_nonneg _))
      (intervalIntegral.integral_nonneg_of_forall (by linarith) hJ0)
  rw [intervalIntegral.integral_add ((hJ.const_mul _).intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hfinal : B / (q.totient : ℝ) * (∫ z in -r..r, J z) +
      (r - -r) * (B * (q.totient : ℝ) * Real.log q ^ 2) ≤
      (2 * B) / (q.totient : ℝ) * (∫ z in -r..r, J z) +
        (2 * B) * (q.totient : ℝ) * r * Real.log q ^ 2 := by
    calc
      _ ≤ 2 * (B / (q.totient : ℝ) * (∫ z in -r..r, J z)) +
          (r - -r) * (B * (q.totient : ℝ) * Real.log q ^ 2) := by linarith
      _ = _ := by ring
  have hh := hgeo.trans (hmono.trans hfinal)
  rw [hsplit] at hh
  exact hh

end LeanLab.Linnik1951
