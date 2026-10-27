/-
P0095 Lu 2010, page 2379 equation 63 and page 2369 equation 39.
CODEX task47, unit U-8103. AI wrote this Lean code. Binary Goldbach is open.
Finite families of primitive characters and critical-strip exponents.
The elementary estimates hold whether or not the exponents are L-function zeros.
Applying them to Lu's complete zero family still requires the cited mass estimate 39.
-/
import LeanLab.ExceptionalSet.Lu2010ZeroIntegral
import LeanLab.ExceptionalSet.Lu2010GaussBound

namespace LeanLab.ExceptionalSet.Lu2010Formula63
open Finset Real ZMod DirichletCharacter
open LeanLab.ExceptionalSet.Lu2010Assembly
open LeanLab.ExceptionalSet.Lu2010ZeroIntegral
open LeanLab.ExceptionalSet.Lu2010GaussBound
open LeanLab.ExceptionalSet.Lu2010Expansion63
open LeanLab.ExceptionalSet.Lu2010Eq86

/-- One primitive character and a critical-strip exponent in the finite sum. -/
structure Exponent where
  label : ℕ := 0
  modulus : ℕ
  modulus_pos : 0 < modulus
  character : DirichletCharacter ℂ modulus
  primitive : character.IsPrimitive
  rho : ℂ
  beta_nonneg : 0 ≤ rho.re
  beta_le_one : rho.re ≤ 1

instance (x : Exponent) : NeZero x.modulus := ⟨x.modulus_pos.ne'⟩

noncomputable def pairMod (p : Exponent × Exponent) : ℕ := Nat.lcm p.1.modulus p.2.modulus

/-- The primitive inducing character extended to a level, with a harmless default off its support. -/
noncomputable def lift (x : Exponent) (q : ℕ) : DirichletCharacter ℂ q :=
  if h : x.modulus ∣ q then changeLevel h x.character else 1

/-- The conjugate primitive character extended to a level. -/
noncomputable def liftInv (x : Exponent) (q : ℕ) : DirichletCharacter ℂ q :=
  if h : x.modulus ∣ q then changeLevel h x.character⁻¹ else 1

/-- The Gauss factor of the conjugate induced character, set to zero at level zero. -/
noncomputable def tau (x : Exponent) (q : ℕ) : ℂ :=
  if hq : 0 < q then
    haveI : NeZero q := ⟨hq.ne'⟩
    gaussSum (liftInv x q) stdAddChar
  else 0

noncomputable def pairChar (p : Exponent × Exponent) (q : ℕ) : DirichletCharacter ℂ q :=
  lift p.1 q * lift p.2 q

noncomputable def W (N : ℕ) (p : Exponent × Exponent) : ℝ :=
  3 * N * weight N p.1.rho * weight N p.2.rho

/-- The zero integral and its Gauss factors after extracting the positive weight. -/
noncomputable def factor (N : ℕ) (p : Exponent × Exponent) (q : ℕ) : ℂ :=
  if pairMod p ∣ q then (J N p.1.rho p.2.rho / (W N p : ℂ)) * (tau p.1 q * tau p.2 q) else 0

/-- The conductor and ordinate restrictions in the outer sum of equation 63. -/
noncomputable def pairs (N : ℕ) (s : Finset Exponent) (M : ℝ) : Finset (Exponent × Exponent) := by
  classical
  exact (s ×ˢ s).filter (fun p =>
    PP N * (N : ℝ) ^ (-0.0001 : ℝ) < pairMod p ∧ (pairMod p : ℝ) ≤ PP N ∧
      |p.1.rho.im| + |p.2.rho.im| ≤ M)

theorem W_pos {N : ℕ} (hN : 1 ≤ N) (p : Exponent × Exponent) : 0 < W N p := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  unfold W weight
  positivity

/-- The actual induced Gauss factors satisfy the size hypothesis of the packet theorem. -/
theorem tau_pair_bound (p : Exponent × Exponent) {q : ℕ} (hq : 1 ≤ q) (hd : pairMod p ∣ q) :
    ‖tau p.1 q * tau p.2 q‖ ≤ (pairMod p : ℝ) := by
  have : NeZero q := ⟨by omega⟩
  have h1 : p.1.modulus ∣ q := (Nat.dvd_lcm_left _ _).trans hd
  have h2 : p.2.modulus ∣ q := (Nat.dvd_lcm_right _ _).trans hd
  have hprim1 : p.1.character⁻¹.IsPrimitive := by
    change p.1.character⁻¹.conductor = p.1.modulus
    rw [conductor_inv]
    exact p.1.primitive
  have hprim2 : p.2.character⁻¹.IsPrimitive := by
    change p.2.character⁻¹.conductor = p.2.modulus
    rw [conductor_inv]
    exact p.2.primitive
  simp only [tau, dite_eq_left (show 0 < q by omega), liftInv, dite_eq_left h1, dite_eq_left h2]
  exact induced_pair_bound _ _ hprim1 hprim2 h1 h2

/-- The complete Gauss and zero-integral factor satisfies the packet bound. -/
theorem factor_bound {N : ℕ} (hN : 1 ≤ N) (p : Exponent × Exponent) (q : ℕ) (hq : 1 ≤ q) :
    ‖factor N p q‖ ≤ (pairMod p : ℝ) := by
  have hW := W_pos hN p
  have hJ : ‖J N p.1.rho p.2.rho‖ ≤ W N p :=
    J_bound hN _ _ p.1.beta_nonneg p.1.beta_le_one p.2.beta_nonneg p.2.beta_le_one
  unfold factor
  split_ifs with hd
  · rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hW.le]
    have hratio : ‖J N p.1.rho p.2.rho‖ / W N p ≤ 1 := (div_le_one hW).mpr hJ
    calc (‖J N p.1.rho p.2.rho‖ / W N p) * ‖tau p.1 q * tau p.2 q‖
        ≤ 1 * (pairMod p : ℝ) :=
          mul_le_mul hratio (tau_pair_bound p hq hd) (norm_nonneg _) (by positivity)
      _ = _ := one_mul _
  · simp

/-- The total extracted weight is at most three N times the squared one-exponent mass. -/
theorem W_total {N : ℕ} (hN : 1 ≤ N) (s : Finset Exponent) (M : ℝ) :
    ∑ p ∈ pairs N s M, W N p ≤ 3 * N * (∑ x ∈ s, weight N x.rho) ^ 2 := by
  classical
  have hsub : pairs N s M ⊆ s ×ˢ s := filter_subset _ _
  refine (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => (W_pos hN p).le)).trans_eq ?_
  rw [sum_product]
  unfold W
  rw [pow_two, sum_mul_sum, mul_sum]
  apply sum_congr rfl
  intro x _
  rw [mul_sum]
  apply sum_congr rfl
  intro y _
  ring

/-- The rational coefficients with the concrete primitive character and integral factors. -/
noncomputable def B (N : ℕ) (s : Finset Exponent) (M : ℝ) : ℕ × ℕ → ℂ :=
  coefficients (pairs N s M) (W N) pairMod (factor N) pairChar

/-- The expanded finite form of equation 63. -/
noncomputable def D6 (N : ℕ) (s : Finset Exponent) (M : ℝ) (k : ℕ) : ℂ :=
  rationalSum ⌊PP N⌋₊ (B N s M) (k : ℤ)

/-- Equation 39, restricted to the finite exponents used in equation 63, is the remaining mass input. -/
def Mass39 (family : ℕ → Finset Exponent) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 1 ≤ N →
    ∑ x ∈ family N, weight N x.rho ≤ C

/-- Expanded coefficients of the finite expression, without normalized weights. -/
theorem B_explicit {N : ℕ} (hN : 1 ≤ N) (s : Finset Exponent) (M : ℝ) (p : ℕ × ℕ) :
    B N s M p = ∑ z ∈ pairs N s M,
      if pairMod z ∣ p.1 then J N z.1.rho z.2.rho * (tau z.1 p.1 * tau z.2 p.1) *
        pairChar z p.1 p.2 / (p.1.totient : ℂ) ^ 2 else 0 := by
  classical
  unfold B coefficients
  apply sum_congr rfl
  intro z _
  have hW : (W N z : ℂ) ≠ 0 := by exact_mod_cast (W_pos hN z).ne'
  unfold packetCoeff factor
  by_cases hd : pairMod z ∣ p.1
  · simp only [hd, ite_true]
    have hc : (W N z : ℂ) * (J N z.1.rho z.2.rho / (W N z : ℂ)) = J N z.1.rho z.2.rho := by
      field_simp
    calc (W N z : ℂ) * ((J N z.1.rho z.2.rho / (W N z : ℂ) * (tau z.1 p.1 * tau z.2 p.1)) *
        pairChar z p.1 p.2 / (p.1.totient : ℂ) ^ 2)
        = ((W N z : ℂ) * (J N z.1.rho z.2.rho / (W N z : ℂ))) *
          (tau z.1 p.1 * tau z.2 p.1) * pairChar z p.1 p.2 / (p.1.totient : ℂ) ^ 2 := by ring
      _ = _ := by rw [hc]
  · simp [hd]

/-- Equation 86 for this concrete finite expression, conditional only on the zero mass of 39. -/
theorem eq86_of_mass39 (family : ℕ → Finset Exponent) (M : ℕ → ℝ) (h39 : Mass39 family) :
    ∃ C86 : ℝ, 0 ≤ C86 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∑ k ∈ Win N, ‖D6 N (family N) (M N) k‖ ^ 2 ≤
        C86 * PP N ^ (-1 : ℝ) * dd N * (N : ℝ) ^ (2.0003 : ℝ) := by
  classical
  obtain ⟨C, hC, N0, hmass⟩ := h39
  obtain ⟨C86, hC86, h86⟩ :=
    LeanLab.ExceptionalSet.Lu2010Eq86Scale.equation86_packets
      (ι := Exponent × Exponent) (Cw := 3 * C ^ 2) (by positivity)
  refine ⟨C86, hC86, max N0 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNm : N0 ≤ N := le_trans (le_max_left _ _) hN
  apply h86 N hN1 (pairs N (family N) (M N)) (W N) pairMod (factor N) pairChar
  · intro p _
    exact (W_pos hN1 p).le
  · intro p hp
    exact (mem_filter.mp hp).2.1.le
  · intro p _ q hq
    exact factor_bound hN1 p q (mem_Icc.mp hq).1
  · have hm0 : 0 ≤ ∑ x ∈ family N, weight N x.rho := by
      apply sum_nonneg
      intro x _
      unfold weight
      positivity
    have hsq := pow_le_pow_left₀ hm0 (hmass N hNm hN1) 2
    calc (∑ p ∈ pairs N (family N) (M N), W N p)
        ≤ 3 * N * (∑ x ∈ family N, weight N x.rho) ^ 2 := W_total hN1 _ _
      _ ≤ 3 * N * C ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (3 * C ^ 2) * N := by ring

end LeanLab.ExceptionalSet.Lu2010Formula63

#print axioms LeanLab.ExceptionalSet.Lu2010Formula63.W_pos
#print axioms LeanLab.ExceptionalSet.Lu2010Formula63.tau_pair_bound
#print axioms LeanLab.ExceptionalSet.Lu2010Formula63.factor_bound
#print axioms LeanLab.ExceptionalSet.Lu2010Formula63.W_total
#print axioms LeanLab.ExceptionalSet.Lu2010Formula63.B_explicit
#print axioms LeanLab.ExceptionalSet.Lu2010Formula63.eq86_of_mass39
