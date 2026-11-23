/-
P0069 Baker Harman Pintz 1997, Theorem 1, a twin route with a coprimality
support hypothesis on the short variable b of Theorem 2.
Background: Section2MS.leaf_minor_local_energy512 is false as stated, see
notes/burst-20261115/BHP1997-falsifier-theorem2.md. The paper's proof of Theorem 2
on pages 7 to 9 tacitly uses that b of m vanishes unless m is coprime to every
modulus q at most Q, true in the paper's only application, Section 5, where the
weights b0 and b1 are supported on m whose prime factors exceed a fixed power of Y.
This file adds that hypothesis, restates the corrected leaves, and threads it to a
twin of theorem1 with exactly the same conclusion. QUESTION for Steve: is this
the faithful reading. AI wrote the Lean code. CLOUD S72. Goldbach is open.
-/
import LeanLab.BHP1997.AssemblyC165

namespace LeanLab.BHP1997.Theorem1CoprimeTwinS72
open Classical Complex Thm2 Section2MS

/-- P0069 pages 7 and 9, the tacit support condition on the short variable b in the
proof of Theorem 2: eventually in x, b x m vanishes for m in the interval J of page 3
unless m is coprime to every modulus q with 1 ≤ q ≤ Q, Q as on page 3. In the paper's
application, Section 5, it holds because b0 and b1 are supported on m all of whose prime
factors exceed Y to a fixed positive power, while Q is below Y to the power 1/16. -/
def CoprimeSupport (ε : ℝ) (b : ℝ → ℕ → ℂ) : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
    ∀ q : ℕ, 1 ≤ q → q ≤ order512 ε x → Nat.gcd m q ≠ 1 → b x m = 0

/-- LEAF: P0069 pages 9 and 10, display 2.11 reduced to 2.12, 2.13 and 2.15, the uniform
local minor arc energy of S2, now with the coprimality support of b used tacitly on
pages 7 to 9. Corrected form of Section2MS.leaf_minor_local_energy512, which is false
without the support condition. Class HARD. -/
theorem leaf_minor_local_energy512_coprime :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Theorem2With ε B (fun _ b _ _ _ => CoprimeSupport ε b →
        ∀ L : ℝ, 0 < L → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
          ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ ζ : ℝ,
            localMinorEnergy512 ε D x (b x) ζ ≤
              C * length512 ε x * Real.log x ^ (-L)) := by
  sorry

/-- P0069 page 6 display 2.3, proved on pages 8 to 10: the minor arc mean square under
the coprimality support of b. Same proof as Section2MS.leaf_minor_arc_mean_square512,
the proved kernel reduction plus the corrected local energy leaf. CONDITIONAL. -/
theorem minor_arc_mean_square512_coprime :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Theorem2With ε B (fun a b _ _ _ => CoprimeSupport ε b →
        ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
          ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
            minorError512 ε D x (a x) (b x) ≤ C * scale512 ε A x) := by
  intro B
  obtain ⟨ε₁, hε₁, hkernel⟩ := leaf_minor_kernel_reduction512 B
  obtain ⟨ε₂, hε₂, hlocal⟩ := leaf_minor_local_energy512_coprime B
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun ε hε hε₀ a b u v E h1 h2 h3 h4 h5 hcop => ?_⟩
  exact (hkernel ε hε (lt_of_lt_of_le hε₀ (min_le_left _ _)) a b u v E h1 h2 h3 h4 h5)
    (hlocal ε hε (lt_of_lt_of_le hε₀ (min_le_right _ _)) a b u v E h1 h2 h3 h4 h5 hcop)

/-- P0069 page 6: the mean square display from the major arc leaf 2.2, unchanged, and the
corrected minor arc estimate 2.3. Twin of Section2MS.section2_mean_square. CONDITIONAL. -/
theorem section2_mean_square_coprime :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Theorem2With ε B (fun a b u v _ => CoprimeSupport ε b → MeanSquare ε a b u v) := by
  intro B
  obtain ⟨ε₁, hε₁, hmajor⟩ := leaf_major_arc_mean_square512 B
  obtain ⟨ε₂, hε₂, hminor⟩ := minor_arc_mean_square512_coprime B
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun ε hε hε₀ a b u v E h1 h2 h3 h4 h5 hcop => ?_⟩
  exact meanSquare_of_arcs512 ε a b u v
    (hmajor ε hε (lt_of_lt_of_le hε₀ (min_le_left _ _)) a b u v E h1 h2 h3 h4 h5)
    (hminor ε hε (lt_of_lt_of_le hε₀ (min_le_right _ _)) a b u v E h1 h2 h3 h4 h5 hcop)

/-- P0069 page 3, Theorem 2 with u v ≠ 0 and the coprimality support of b, by the page 6
reduction conclusion_of_meanSquare. Twin of Section2MS.theorem2_paper_nondegenerate.
CONDITIONAL. -/
theorem theorem2_coprime_nondegenerate :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Theorem2With ε B (fun a b u v _ =>
        CoprimeSupport ε b → u * v ≠ 0 → Conclusion ε a b u v) := by
  intro B
  obtain ⟨ε₀, hε₀, h⟩ := section2_mean_square_coprime B
  refine ⟨ε₀, hε₀, fun ε hε hεε a b u v E h1 h2 h3 h4 h5 hcop huv => ?_⟩
  exact conclusion_of_meanSquare ε hε a b u v huv (h ε hε hεε a b u v E h1 h2 h3 h4 h5 hcop)

/-- Corrected Theorem 2 of P0069 page 3: Section2Q2.Theorem2Pos with the added hypothesis
that b has the coprimality support used tacitly on pages 7 and 9. -/
def Theorem2PosCoprime (ε B : ℝ) : Prop :=
  Theorem2With ε B (fun a b u v _ => CoprimeSupport ε b → 0 < u → 0 < v → Conclusion ε a b u v)

/-- P0069 page 3, the corrected positive Theorem 2 in the window of ε. Twin of
Section2Q2.theorem2Pos_paper_of_leaf. CONDITIONAL on the corrected leaf. -/
theorem theorem2PosCoprime_paper :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → Theorem2PosCoprime ε B := by
  intro B
  obtain ⟨ε₀, hε₀, h⟩ := theorem2_coprime_nondegenerate B
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  exact theorem2With_mono (fun _ _ u v _ hc hs hu hv => hc hs (mul_ne_zero hu.ne' hv.ne'))
    (h ε hε hεε)

end LeanLab.BHP1997.Theorem1CoprimeTwinS72

namespace LeanLab.BHP1997.DecompC165b.CoprimeTwinS72
open Classical Complex Decomp132
open LeanLab.BHP1997.Theorem1CoprimeTwinS72

/-- LEAF: P0069 Section 5, pages 25 to 40, the weights b0 and b1 of Section 5 with all the
properties of DecompC165b.section5_weights and in addition the support fact: b0 and b1
vanish on m with a prime factor below Y to the power c1, c1 about 1/8, so, since
Q < Y to the 1/16, b0 x m = b1 x m = 0 whenever m shares a factor with some q ≤ Q.
The lab states the Section 5 weights only existentially, so the support fact is carried
here together with them. Class HARD. -/
theorem section5_weights_coprime (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v0 v1 : ℝ) (b0 b1 : ℝ → ℕ → ℝ),
        0.05 < v0 ∧ v0 ≤ v1 ∧ v1 < 2.2 ∧
        RightConditions ε B v0 b0 ∧ RightConditions ε B v1 b1 ∧
        (∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x,
            b0 x m ≤ primeWeight m ∧ primeWeight m ≤ b1 x m) ∧
        CoprimeSupport ε (fun x m => (b0 x m : ℂ)) ∧
        CoprimeSupport ε (fun x m => (b1 x m : ℂ)) := by
  sorry

/-- Page 3, the corrected Theorem 2 applied to one pair of real weights; copy of
DecompC165b.pair_correlation_pos with the coprimality support of b added. CONDITIONAL. -/
theorem pair_correlation_coprime {ε B u v : ℝ} {a b : ℝ → ℕ → ℝ}
    (h2 : Theorem2PosCoprime ε B) (hu : 0 < u) (hv : 0 < v) (ha : LeftConditions ε B u a)
    (hb : RightConditions ε B v b)
    (hsupp : CoprimeSupport ε (fun x m => (b x m : ℂ))) :
    ∀ A : ℝ, 0 < A → ∃ K C : ℝ, ∀ x : ℝ, C ≤ x →
      ((badSet ε u v K a b x).card : ℝ) <
        x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) / Real.log x ^ A := by
  obtain ⟨hai, ⟨Ca, hCa⟩, harough⟩ := ha
  obtain ⟨⟨Cb, hCb⟩, hbiii, E, hbiv⟩ := hb
  have hdiv : ∃ C : ℝ, ∀ x k,
      ‖(a x k : ℂ)‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B ∧
      ‖(b x k : ℂ)‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B := by
    refine ⟨max Ca Cb, ?_⟩
    intro x k
    have hpow : 0 ≤ ((k.divisors.card : ℕ) : ℝ) ^ B := Real.rpow_nonneg (by positivity) _
    constructor
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (hCa x k).trans (mul_le_mul_of_nonneg_right (le_max_left Ca Cb) hpow)
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (hCb x k).trans (mul_le_mul_of_nonneg_right (le_max_right Ca Cb) hpow)
  have hrough : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
      Nat.gcd k (Thm2.primorialBelow (Real.log x ^ A)) ≠ 1 → (a x k : ℂ) = 0 := by
    intro A hA
    obtain ⟨C, hC⟩ := harough A hA
    exact ⟨C, fun x hx k hk => by simp [hC x hx k hk]⟩
  have hout := h2 (fun x k => (a x k : ℂ)) (fun x k => (b x k : ℂ)) u v E
    hai hdiv hrough hbiii (by simpa only [sieveQ, rightInterval] using hbiv) hsupp hu hv
  intro A hA
  obtain ⟨K, C, hC⟩ := hout A hA
  refine ⟨K, C, fun x hx => ?_⟩
  have hc := hC x hx
  convert hc using 1
  congr 2
  apply Finset.filter_congr
  intro N hN
  have hconv : (∑ k ∈ leftInterval ε x, ∑ m ∈ rightInterval ε x,
      if k + m = N then (a x k : ℂ) * (b x m : ℂ) else 0) =
      (convolution (leftInterval ε x) (rightInterval ε x) (a x) (b x) N : ℂ) := by
    simp only [convolution, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro m hm
    split_ifs <;> simp
  simp only [correlationScale, leftInterval, rightInterval] at *
  rw [hconv]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_div, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  ring_nf
/-- Pages 2 to 4, the correlation transfer; copy of DecompC165b.correlation_transfer_pos
with the corrected Theorem 2 and the support of b0 and b1. CONDITIONAL. -/
theorem correlation_transfer_coprime
    {ε B u0 u1 v0 v1 : ℝ} {a0 a1 b0 b1 : ℝ → ℕ → ℝ}
    (h2 : Theorem2PosCoprime ε B)
    (hε : 0 < ε) (hε1 : ε < 8.8 / 10 ^ 5)
    (hu0 : 0.99 < u0) (hu : u0 ≤ u1) (hu1 : u1 < 1.01)
    (hv0 : 0.05 < v0) (hv : v0 ≤ v1) (hv1 : v1 < 2.2)
    (ha0 : LeftConditions ε B u0 a0) (ha1 : LeftConditions ε B u1 a1)
    (hb0 : RightConditions ε B v0 b0) (hb1 : RightConditions ε B v1 b1)
    (hsupp0 : CoprimeSupport ε (fun x m => (b0 x m : ℂ)))
    (hsupp1 : CoprimeSupport ε (fun x m => (b1 x m : ℂ)))
    (hsand : ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      (∀ k ∈ leftInterval ε x, a0 x k ≤ primeWeight k ∧ primeWeight k ≤ a1 x k) ∧
      (∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m ∧ primeWeight m ≤ b1 x m)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
        ∃ (I J : Finset ℕ) (a0 a1 b0 b1 : ℕ → ℝ) (E : Finset ℕ),
          (∀ k ∈ I, a0 k ≤ primeWeight k ∧ primeWeight k ≤ a1 k) ∧
          (∀ m ∈ J, b0 m ≤ primeWeight m ∧ primeWeight m ≤ b1 m) ∧
          (E.card : ℝ) < x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) /
            Real.log x ^ A ∧
          ∀ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊,
            Even N → N ∉ E → ∃ r : ℝ, 0 < r ∧
              |convolution I J a0 b1 N - u0 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b0 N - u1 * v0 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b1 N - u1 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 := by
  have hpos_u0 : 0 < u0 := by linarith
  have hpos_u1 : 0 < u1 := by linarith
  have hpos_v0 : 0 < v0 := by linarith
  have hpos_v1 : 0 < v1 := by linarith
  intro A hA
  obtain ⟨K01, C01, h01⟩ := pair_correlation_coprime h2 hpos_u0 hpos_v1 ha0 hb1 hsupp1 (A + 1) (by linarith)
  obtain ⟨K10, C10, h10⟩ := pair_correlation_coprime h2 hpos_u1 hpos_v0 ha1 hb0 hsupp0 (A + 1) (by linarith)
  obtain ⟨K11, C11, h11⟩ := pair_correlation_coprime h2 hpos_u1 hpos_v1 ha1 hb1 hsupp1 (A + 1) (by linarith)
  obtain ⟨Xs, hs⟩ := hsand
  let m := u0 * v1 + u1 * v0 - u1 * v1
  have hm : 0 < m := constants15 hu0 hu hu1 hv0 hv hv1
  let D := max 1 (max (max (K01 * |u0 * v1|) (K10 * |u1 * v0|)) (K11 * |u1 * v1|))
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hD01 : K01 * |u0 * v1| ≤ D :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hD10 : K10 * |u1 * v0| ≤ D :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hD11 : K11 * |u1 * v1| ≤ D := le_trans (le_max_right _ _) (le_max_right _ _)
  let R := 4 + 6 * D / m
  let X := max (max Xs C01) (max (max C10 C11) (Real.exp (R + 1)))
  refine ⟨X, fun x hx => ?_⟩
  have hxS : Xs ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx01 : C01 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx10 : C10 ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have hx11 : C11 ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have hxexp : Real.exp (R + 1) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hR : 4 < R := by
    have hp : 0 < 6 * D / m := by positivity
    dsimp [R]
    linarith
  have hx1 : 1 < x := lt_of_lt_of_le
    (Real.one_lt_exp_iff.mpr (by linarith)) hxexp
  have hx0 : 0 < x := by linarith
  have hlogR : R + 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos _) hxexp
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hlog3 : 3 < Real.log x := by linarith
  have hDlog : 6 * D ≤ m * Real.log x := by
    have ht : 6 * D / m ≤ Real.log x := by dsimp [R] at hlogR; linarith
    have hh := (div_le_iff₀ hm).mp ht
    nlinarith
  let E01 := badSet ε u0 v1 K01 a0 b1 x
  let E10 := badSet ε u1 v0 K10 a1 b0 x
  let E11 := badSet ε u1 v1 K11 a1 b1 x
  let E := (E01 ∪ E10) ∪ E11
  refine ⟨leftInterval ε x, rightInterval ε x, a0 x, a1 x, b0 x, b1 x, E,
    (hs x hxS).1, (hs x hxS).2, ?_, ?_⟩
  · have hcard : E.card ≤ E01.card + E10.card + E11.card :=
      (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have hcast : (E.card : ℝ) ≤ (E01.card : ℝ) + (E10.card : ℝ) + (E11.card : ℝ) := by
      exact_mod_cast hcard
    have hc01 := h01 x hx01
    have hc10 := h10 x hx10
    have hc11 := h11 x hx11
    have hsmall : (E.card : ℝ) <
        3 * (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) / Real.log x ^ (A + 1)) := by
      dsimp only [E01, E10, E11] at hcast
      linarith
    apply lt_trans hsmall
    rw [← mul_div_assoc, Real.rpow_add hlog, Real.rpow_one,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    have hp : 0 < x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * Real.log x ^ A := by
      positivity
    nlinarith [mul_lt_mul_of_pos_left hlog3 hp]
  · intro N hN hEven hNE
    let r := correlationScale ε x N
    have hr : 0 < r := by
      dsimp [r, correlationScale]
      have hlogY : 0 < Real.log (x ^ (11 / 20 + ε)) := by
        rw [Real.log_rpow hx0]
        positivity
      exact mul_pos (div_pos (Real.rpow_pos_of_pos hx0 _) (mul_pos hlog hlogY)) (Thm2.sing_pos _)
    refine ⟨r, hr, ?_, ?_, ?_⟩
    all_goals
      have hnot01 : N ∉ E01 := by
        intro hn
        apply hNE
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hn)
      have hnot10 : N ∉ E10 := by
        intro hn
        apply hNE
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hn)
      have hnot11 : N ∉ E11 := by
        intro hn
        apply hNE
        exact Finset.mem_union_right _ hn
      have hbound (u v K : ℝ) (a b : ℝ → ℕ → ℝ)
          (hn : N ∉ badSet ε u v K a b x) (hK : K * |u * v| ≤ D) :
          |convolution (leftInterval ε x) (rightInterval ε x) (a x) (b x) N - u * v * r| ≤ m * r / 6 := by
        have he : |convolution (leftInterval ε x) (rightInterval ε x) (a x) (b x) N - u * v * r| ≤
            K * |u * v| * r / Real.log x := by
          apply le_of_not_gt
          intro hbad
          exact hn (Finset.mem_filter.mpr ⟨hN, hEven, hbad⟩)
        apply he.trans
        apply (div_le_iff₀ hlog).mpr
        have h1 := mul_le_mul_of_nonneg_right hK hr.le
        have h2 := mul_le_mul_of_nonneg_right hDlog hr.le
        nlinarith
    · exact hbound u0 v1 K01 a0 b1 hnot01 hD01
    · exact hbound u1 v0 K10 a1 b0 hnot10 hD10
    · exact hbound u1 v1 K11 a1 b1 hnot11 hD11
/-- Pages 1 to 4 and Sections 2 to 5: twin of DecompC165b.sieve_data with the same
statement, using the corrected Theorem 2 and the Section 5 weights with their support
fact. CONDITIONAL on the two LEAFs of this file and the other named analytic inputs. -/
theorem sieve_data_coprime :
    ∃ ε u0 u1 v0 v1 : ℝ, 0 < ε ∧ ε < 8.8 / 10 ^ 5 ∧
      0.99 < u0 ∧ u0 ≤ u1 ∧ u1 < 1.01 ∧ 0.05 < v0 ∧ v0 ≤ v1 ∧ v1 < 2.2 ∧
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
        ∃ (I J : Finset ℕ) (a0 a1 b0 b1 : ℕ → ℝ) (E : Finset ℕ),
          (∀ k ∈ I, a0 k ≤ primeWeight k ∧ primeWeight k ≤ a1 k) ∧
          (∀ m ∈ J, b0 m ≤ primeWeight m ∧ primeWeight m ≤ b1 m) ∧
          (E.card : ℝ) < x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) /
            Real.log x ^ A ∧
          ∀ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊,
            Even N → N ∉ E → ∃ r : ℝ, 0 < r ∧
              |convolution I J a0 b1 N - u0 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b0 N - u1 * v0 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b1 N - u1 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 := by
  have h4 := section3_mean_values
  obtain ⟨Bl, ηl, hηl, hl⟩ := section4_lower h4
  obtain ⟨Bu, ηu, hηu, hu⟩ := section4_upper h4
  obtain ⟨Br, ηr, hηr, hr⟩ := section5_weights_coprime h4 DecompC165a.lemma9
  obtain ⟨η2, hη2, h2⟩ := theorem2PosCoprime_paper (max Bl (max Bu Br))
  let η := min η2 (min ηl (min ηu (min ηr (8.8 / 10 ^ 5))))
  have hη : 0 < η := by dsimp [η]; positivity
  let ε := η / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεη : ε < η := by dsimp [ε]; linarith
  have hε2 : ε < η2 := lt_of_lt_of_le hεη (min_le_left _ _)
  have hεl : ε < ηl := lt_of_lt_of_le hεη
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεu : ε < ηu := lt_of_lt_of_le hεη
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hεr : ε < ηr := lt_of_lt_of_le hεη
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hε1 : ε < 8.8 / 10 ^ 5 := lt_of_lt_of_le hεη
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
  let B := max Bl (max Bu Br)
  obtain ⟨u0, a0, hu0, hu01, ha0, X0, hs0⟩ := hl B ε (le_max_left _ _) hε hεl
  obtain ⟨u1, a1, hu11, hu1, ha1, X1, hs1⟩ := hu B ε
    (le_trans (le_max_left _ _) (le_max_right _ _)) hε hεu
  obtain ⟨v0, v1, b0, b1, hv0, hv, hv1, hb0, hb1, ⟨Xb, hsb⟩, hc0, hc1⟩ := hr B ε
    (le_trans (le_max_right _ _) (le_max_right _ _)) hε hεr
  have hu0' : 0.99 < u0 := by linarith
  have hu' : u0 ≤ u1 := le_trans hu01 hu11
  have hu1' : u1 < 1.01 := by linarith
  refine ⟨ε, u0, u1, v0, v1, hε, hε1, hu0', hu', hu1', hv0, hv, hv1, ?_⟩
  exact correlation_transfer_coprime (h2 ε hε hε2) hε hε1 hu0' hu' hu1' hv0 hv hv1
    ha0 ha1 hb0 hb1 hc0 hc1 ⟨max X0 (max X1 Xb), fun x hx =>
      ⟨fun k hk => ⟨hs0 x (le_trans (le_max_left _ _) hx) k hk,
        hs1 x (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) k hk⟩,
       hsb x (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx)⟩⟩

end LeanLab.BHP1997.DecompC165b.CoprimeTwinS72

namespace LeanLab.BHP1997.Theorem1CoprimeTwinS72
open Classical Real Filter Decomp132

/-- P0069 Theorem 1, pages 1 to 4: twin of AssemblyC165.theorem1 with exactly its
conclusion, following the same finite deduction but from sieve_data_coprime, which avoids
the false leaf Section2MS.leaf_minor_local_energy512. CONDITIONAL on
leaf_minor_local_energy512_coprime, section5_weights_coprime and the other named inputs.
QUESTION for Steve: is the coprimality support the faithful reading of pages 7 and 9. -/
theorem theorem1_coprime_twin : Theorem1 := by
  obtain ⟨ε, u0, u1, v0, v1, hε, hε1, hu0, hu, hu1, hv0, hv, hv1, hdata⟩ :=
    DecompC165b.CoprimeTwinS72.sieve_data_coprime
  have hm := constants15 hu0 hu hu1 hv0 hv hv1
  have hδ := theta12 hε hε1
  intro θ hθ
  apply cover_short_intervals (by linarith : 0 < (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))
    (by linarith : (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) < 1)
    (lt_of_lt_of_le hδ.1 hθ)
  intro A hA
  obtain ⟨C, hC⟩ := hdata A hA
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨I, J, a0, a1, b0, b1, E, ha, hb, hE, hcorr⟩ := hC x hx
  have hsub : (Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
      (fun N => Even N ∧ ¬ IsGoldbachSum N) ⊆ E := by
    intro N hN
    obtain ⟨hNI, hEven, hnot⟩ := Finset.mem_filter.mp hN
    by_contra hNE
    obtain ⟨r, hr, h01, h10, h11⟩ := hcorr N hNI hEven hNE
    have hpos := correlation_positive hm hr h01 h10 h11
    have hle := convolution_sandwich ha hb N
    rw [prime_convolution_zero I J hnot] at hle
    linarith
  exact lt_of_le_of_lt (by exact_mod_cast Finset.card_le_card hsub) hE


end LeanLab.BHP1997.Theorem1CoprimeTwinS72
