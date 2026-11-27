/-
P0069 Baker Harman Pintz 1997, pages 9 and 10, displays 2.11 to 2.16.
CLOUD S130 split of Theorem1CoprimeTwinS72.leaf_minor_local_energy512_coprime along the
paper: the rational arc and exceptional character step 2.11 to 2.15, now under the
coprimality support of b, is a new LEAF; Gallagher 2.16 is the PROVED
Decomp561d.leaf_gallagher561 and the Saffari Vaughan window comparison is the existing
LEAF Decomp561d.leaf_saffari_vaughan561. The assembly copies Decomp561d.local_minor_energy561.
AI wrote the Lean code. CLOUD S130. Goldbach is open.
-/
import LeanLab.BHP1997.Theorem1CoprimeTwinS72
import LeanLab.BHP1997.Decomp561d

namespace LeanLab.BHP1997.S130CoprimeLocalEnergy
open Classical Complex Thm2 Section2MS
open LeanLab.BHP1997.Theorem1CoprimeTwinS72

/-- LEAF: P0069 page 9 displays 2.11 to 2.14 and page 10 display 2.15, the rational arc
covering of a minor arc neighbourhood, the principal part and the exceptional characters by
Parseval, reducing the local energy of S2 to the complementary character energy of the
centred coefficients; with the coprimality support of b used tacitly on pages 7 to 9, so that
the expansion of S2 at a/q in characters mod q is exact. Corrected form of
Decomp561d.leaf_local_energy_from_characters561, which carries no support hypothesis.
The Gallagher step 2.16 and the Saffari Vaughan comparison are not in this leaf. Class HARD. -/
theorem leaf_local_energy_from_characters_coprime :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Theorem2With ε B (fun _ b _ v E => CoprimeSupport ε b →
        (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          ∀ q : ℕ, 1 ≤ q → q ≤ order512 ε x →
            Decomp561d.characterEnergy561 (length512 ε x) ((q : ℝ) * order512 ε x) (b x) v q
              (E A x q) ≤ C * length512 ε x * Real.log x ^ (-A)) →
        ∀ L : ℝ, 0 < L → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
          ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ ζ : ℝ,
            localMinorEnergy512 ε D x (b x) ζ ≤
              C * length512 ε x * Real.log x ^ (-L)) := by
  intro B
  exact Decomp561d.leaf_local_energy_from_characters561 B

/-- P0069 pages 9 and 10 displays 2.11 to 2.16: the corrected local minor arc energy,
exactly the statement of Theorem1CoprimeTwinS72.leaf_minor_local_energy512_coprime, from the
corrected rational arc leaf above, Gallagher 2.16 and the Saffari Vaughan comparison after
2.16 with hypothesis iv of Theorem 2. Same proof as Decomp561d.local_minor_energy561.
CONDITIONAL on leaf_local_energy_from_characters_coprime and
Decomp561d.leaf_saffari_vaughan561. -/
theorem leaf_minor_local_energy512_coprime_of_s130 :
    type_of% @Theorem1CoprimeTwinS72.leaf_minor_local_energy512_coprime := by
  intro B
  obtain ⟨ε₀, hε₀, hlocal⟩ := leaf_local_energy_from_characters_coprime B
  obtain ⟨G, hG, hGall⟩ := Decomp561d.leaf_gallagher561
  obtain ⟨V, hV, hSV⟩ := Decomp561d.leaf_saffari_vaughan561
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε he a b u v E
  dsimp only
  intro h1 h2 h3 h4 h5 hcop
  apply hlocal ε hε he a b u v E h1 h2 h3 h4 h5 hcop
  intro A hA
  obtain ⟨C₀, hC₀⟩ := h5 A hA
  let C : ℝ := max (max C₀ 3) (G * V * |C₀|)
  refine ⟨C, fun x hx q hq hqQ => ?_⟩
  have hxC : C₀ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx3 : 3 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hY : 1 ≤ length512 ε x :=
    Real.one_le_rpow (by linarith) (by linarith)
  have hQ : 1 ≤ order512 ε x := hq.trans hqQ
  let Y := length512 ε x
  let T : ℝ := (q : ℝ) * order512 ε x
  have hY0 : 0 ≤ Y := by dsimp [Y]; linarith
  have hT : 0 < T := by
    dsimp [T]
    exact mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq))
      (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ))
  have hTY : T ≤ Y := by
    calc
      T ≤ (order512 ε x : ℝ) ^ 2 := by
        dsimp [T]
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hqQ) (Nat.cast_nonneg _)
      _ ≤ Y := Decomp561d.order_square_le_length561 ε x hY
  let M : ℝ := |C₀| * T ^ 2 * Y * Real.log x ^ (-A)
  have hlog0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hmulti (z : ℝ) (hz0 : T / (6 * Y) ≤ z) (hz1 : z ≤ 6 * T / Y) :
      Decomp561d.multiplicativeWindowMoment561 Y z (b x) v q (E A x q) ≤ M := by
    have hh := (hC₀ x hxC q hq hqQ).2 z hz0
      (by simpa [T, Y, length512, order512, mul_assoc] using hz1)
    change Decomp561d.multiplicativeWindowMoment561 Y z (b x) v q (E A x q) ≤
      C₀ * T ^ 2 * Y * Real.log x ^ (-A) at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self C₀) (sq_nonneg T)) hY0)
      (Real.rpow_nonneg hlog0.le _))
  have hfixed := hSV Y T hY hT hTY (b x) v q (E A x q) M hM hmulti
  have henergy := hGall Y T hY hT hTY (b x) v q (E A x q)
  calc
    Decomp561d.characterEnergy561 Y T (b x) v q (E A x q) ≤
        G / T ^ 2 * Decomp561d.fixedWindowMoment561 Y T (b x) v q (E A x q) := henergy
    _ ≤ G / T ^ 2 * (V * M) := mul_le_mul_of_nonneg_left hfixed (by positivity)
    _ = (G * V * |C₀|) * Y * Real.log x ^ (-A) := by
      dsimp [M]
      field_simp [ne_of_gt hT]
    _ ≤ C * Y * Real.log x ^ (-A) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hY0)
        (Real.rpow_nonneg hlog0.le _)

end LeanLab.BHP1997.S130CoprimeLocalEnergy
