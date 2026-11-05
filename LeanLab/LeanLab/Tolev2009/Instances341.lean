/-
AI wrote this Lean code. Codex task341.
Binary Goldbach is open.
Source context: Tolev 1999 page 83 display 54 and the adapted Type II shell.
These nonzero instances test the exact geometric and minor arc hypotheses.
-/
import LeanLab.Tolev2009.Decomp341c
import LeanLab.Tolev2009.Instances336

open Finset Real
namespace LeanLab.Tolev2009.Instances341
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Decomp286b LeanLab.Tolev2009.Decomp310a
open LeanLab.Tolev2009.Decomp310b LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Instances336

/-- Every positive integer has at least one ordered factorization into five factors.
This supplies a nonzero coefficient instance for display 54. -/
theorem one_le_tau5 (n : ℕ) (hn : 1≤n) : 1≤tau5 n := by
  have hp : ∀ k : ℕ, 1≤(ArithmeticFunction.zeta^(k+1)) n := by
    intro k
    induction k with
    | zero => simp [ArithmeticFunction.zeta_apply_ne (by omega : n≠0)]
    | succ k ih =>
      rw [pow_succ,ArithmeticFunction.mul_zeta_apply]
      exact ih.trans (single_le_sum (fun d hd => Nat.zero_le _) (Nat.mem_divisors.mpr ⟨dvd_refl n,by omega⟩))
  exact hp 4

/-- A one frequency second coefficient gives a nonzero energy term.
All shell and product cutoffs of the source row are retained. -/
theorem indicator_energy (N K m l : ℕ) (α x M M₁ H H₁ : ℝ)
    (hK : 1≤K) (hm : m∈Ioc ⌊M⌋₊ ⌊M₁⌋₊) (hl : l∈Ioc ⌊H⌋₊ ⌊H₁⌋₊)
    (hprod : x<(m*l:ℕ) ∧ (m*l:ℕ)≤2*x ∧ m*l≤N) :
    1≤energy (fun k => if k=1 then 1 else 0) 1 K N α x M M₁ H H₁
      (fun j => if j=l then 1 else 0) := by
  classical
  have he : row (fun k => if k=1 then 1 else 0) 1 K N α x H H₁
      (fun j => if j=l then 1 else 0) m = ee (α*(m*l:ℕ)) := by
    unfold row
    rw [sum_eq_single l]
    · rw [if_pos hprod]
      simp only [ite_true,unit_weight_eq_one (m*l) K hK,Complex.ofReal_one,one_mul,mul_one]
    · intro j hj hne
      simp [hne]
    · intro hnot
      exact False.elim (hnot hl)
  have hh := single_le_sum (s:=Ioc ⌊M⌋₊ ⌊M₁⌋₊)
    (f:=fun u => ‖row (fun k => if k=1 then 1 else 0) 1 K N α x H H₁
      (fun j => if j=l then 1 else 0) u‖^2) (fun u hu => sq_nonneg _) hm
  simpa only [energy,he,norm_ee,one_pow] using hh

/-- Cubic factor pairs satisfy both Type II second variable scale bounds.
This is a nonvacuity check for Tolev 1999 display 54. -/
theorem cubic_scales (t : ℕ) (ht : 4≤t) :
    let x : ℝ := (t:ℝ)^3-1
    x^((1:ℝ)/1000) ≤ (t:ℝ)/2 ∧ (t:ℝ)/2 ≤ 2^(30:ℕ)*x^((1:ℝ)/3) := by
  dsimp only
  have htR : (4:ℝ)≤t := by exact_mod_cast ht
  have htp : (0:ℝ)<t := by linarith
  have ht3 : (64:ℝ)≤(t:ℝ)^3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤4) htR 3]
  have hxp : 0<(t:ℝ)^3-1 := by linarith
  constructor
  · calc
      _ ≤ ((t:ℝ)^3)^((1:ℝ)/1000) := Real.rpow_le_rpow hxp.le (by linarith) (by norm_num)
      _ = (t:ℝ)^((3:ℝ)/1000) := by rw [← Real.rpow_natCast,← Real.rpow_mul htp.le]; norm_num
      _ ≤ (t:ℝ)^((1:ℝ)/2) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ ≤ (t:ℝ)/2 := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith⟩
  · have hx : ((t:ℝ)/2)^3 ≤ (t:ℝ)^3-1 := by nlinarith
    have hroot := Real.rpow_le_rpow (by positivity : 0≤((t:ℝ)/2)^3) hx (by norm_num : (0:ℝ)≤1/3)
    have he : (((t:ℝ)/2)^3)^((1:ℝ)/3) = (t:ℝ)/2 := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity : 0≤(t:ℝ)/2)]
      norm_num
    rw [he] at hroot
    exact hroot.trans (by have := Real.rpow_nonneg hxp.le ((1:ℝ)/3); nlinarith)

/-- Nonzero Type II energy occurs above every threshold on the sealed minor arcs.
The witnesses have N equal to twice t cubed plus one and product t squared times t. -/
theorem nonzero_minor_arc_energy (A : ℝ) (hA : 10000≤A) (T : ℝ) :
    ∃ (N : ℕ) (α x M H : ℝ) (b : ℕ → ℂ),
      Odd N ∧ T≤N ∧
      α∈Set.Ioo (-1/τof A N) (1-1/τof A N) ∧ α∉majorArcs (Qof A N) (τof A N) ∧
      (N:ℝ)*Real.log N^(-4*A)≤x ∧ x≤N ∧ 2<x ∧ 0<M ∧ 0<H ∧
      x/4≤M*H ∧ M*H≤2*x ∧ x^((1:ℝ)/1000)≤H ∧ H≤2^(30:ℕ)*x^((1:ℝ)/3) ∧
      (∀ l, ‖b l‖≤(tau5 l:ℝ)*Real.log N) ∧
      1≤energy (fun k => if k=1 then 1 else 0) 1 (cutoff3 (10000*A) N) N α x M (2*M) H (2*H) b := by
  obtain ⟨N₀,hparam⟩ := eventual_nonvacuity_parameters A (by linarith)
  obtain ⟨t,ht⟩ := exists_nat_gt (max (max N₀ T) 8)
  have ht8 : (8:ℝ)<t := (le_max_right _ _).trans_lt ht
  have ht8n : 8≤t := by exact_mod_cast ht8.le
  have htp : (0:ℝ)<t := by linarith
  let N := 2*t^3+1
  let x : ℝ := (t:ℝ)^3-1
  let M : ℝ := (t:ℝ)^2/2
  let H : ℝ := (t:ℝ)/2
  let b : ℕ → ℂ := fun l => if l=t then 1 else 0
  have ht3 : (t:ℝ)≤(t:ℝ)^3 := by nlinarith [sq_nonneg ((t:ℝ)-1)]
  have htN : (t:ℝ)≤N := by dsimp [N]; push_cast; nlinarith
  have hN₀ : N₀≤N := ((le_max_left _ _).trans ((le_max_left _ _).trans ht.le)).trans htN
  have hNT : T≤N := ((le_max_right _ _).trans ((le_max_left _ _).trans ht.le)).trans htN
  obtain ⟨hL,hτ,hK⟩ := hparam N hN₀
  have hLp : 0<Real.log N := by linarith
  have hQ : 1≤Qof A N := Real.one_le_rpow (by linarith) (by nlinarith)
  obtain ⟨hα,hminor⟩ := rational_minor_point (Qof A N) (τof A N) hQ hτ
  let α : ℝ := 1/((⌊Qof A N⌋₊+1:ℕ):ℝ)
  have hNp : (N:ℝ)=2*(t:ℝ)^3+1 := by dsimp [N]; push_cast; ring
  have hx : 2<x := by dsimp [x]; nlinarith
  have hxN : x≤N := by dsimp [x]; nlinarith
  have hsmall : Real.log N^(-4*A)≤(1:ℝ)/4 := by
    calc
      _ ≤ Real.log N^(-(2:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ (2:ℝ)^(-(2:ℝ)) := Real.rpow_le_rpow_of_nonpos (by norm_num) hL (by norm_num)
      _ = _ := by norm_num
  have hxlo : (N:ℝ)*Real.log N^(-4*A)≤x := by
    have ht := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg N)
    dsimp [x]
    nlinarith
  have hM : 0<M := by dsimp [M]; positivity
  have hH : 0<H := by dsimp [H]; positivity
  obtain ⟨hHlo,hHhi⟩ := cubic_scales t (by omega)
  have hprodlo : x/4≤M*H := by dsimp [x,M,H]; nlinarith
  have hprodhi : M*H≤2*x := by dsimp [x,M,H]; nlinarith
  have hb : ∀ l, ‖b l‖≤(tau5 l:ℝ)*Real.log N := by
    intro l
    dsimp [b]
    split_ifs with he
    · subst l
      have hτ5 : (1:ℝ)≤tau5 t := by exact_mod_cast one_le_tau5 t (by omega)
      norm_num only [norm_one]
      nlinarith
    · simp only [norm_zero]
      positivity
  have hm : t^2∈Ioc ⌊M⌋₊ ⌊2*M⌋₊ := by
    apply mem_Ioc.mpr
    constructor
    · apply (Nat.floor_lt (by positivity : (0:ℝ)≤M)).mpr
      dsimp [M]
      push_cast
      nlinarith [sq_pos_of_pos htp]
    · apply Nat.le_floor
      dsimp [M]
      push_cast
      nlinarith
  have hl : t∈Ioc ⌊H⌋₊ ⌊2*H⌋₊ := by
    apply mem_Ioc.mpr
    constructor
    · apply (Nat.floor_lt (by positivity : (0:ℝ)≤H)).mpr
      dsimp [H]
      linarith
    · apply Nat.le_floor
      dsimp [H]
      linarith
  have hproduct : x<(t^2*t:ℕ) ∧ (t^2*t:ℕ)≤2*x ∧ t^2*t≤N := by
    dsimp [x,N]
    push_cast
    constructor
    · nlinarith
    constructor <;> nlinarith
  refine ⟨N,α,x,M,H,b,⟨t^3,rfl⟩,hNT,hα,hminor,hxlo,hxN,hx,hM,hH,hprodlo,hprodhi,hHlo,hHhi,hb,?_⟩
  exact indicator_energy N (cutoff3 (10000*A) N) (t^2) t α x M (2*M) H (2*H) hK hm hl hproduct

end LeanLab.Tolev2009.Instances341
