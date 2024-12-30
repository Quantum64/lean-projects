import Mathlib
import Paperproof

open Nat
open PNat
open Finset

namespace Nat

def order (a n : ℕ) : ℕ :=
  n - Nat.findGreatest (λ i => a ^ (n - i) ≡ 1 [MOD n]) (n - 1)

@[reducible] def PrimitiveRoot (g n : ℕ) : Prop :=
   order g n = n - 1

variable {a n g : ℕ} {hg : g.PrimitiveRoot n}
variable {p : ℕ}

def index (a n g : ℕ) : ℕ := Nat.findGreatest (λ i => g ^ i ≡ a [MOD n]) (n - 1)


theorem order_def (hp : Nat.Prime p) : a ^ (order a p) ≡ 1 [MOD p] := by
  unfold order
  by_cases h : findGreatest (fun i => a ^ (p - i) ≡ 1 [MOD p]) (p - 1) = 0
  . simp_all
    rw [Nat.findGreatest_eq_zero_iff] at h
    refine modEq_of_dvd ?_
    simp_all
    by_cases h2 : a ^ p = 0
    . simp_all
      exfalso
  . rw [Nat.findGreatest_eq_zero_iff] at h
    push_neg at h
    obtain ⟨i, hi, h⟩ := h


theorem order_dvd (h : a ^ n ≡ 1 [MOD p]) (hp : PNat.Prime p) (hn : n > 0) (ha : ¬a ∣ p) : order a p ∣ n := by
  have a_pos : 0 < a := by
    by_contra hneg
    have : a = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt hneg)
    simp [this] at h
    rw [Nat.zero_pow, ModEq.comm, Nat.modEq_zero_iff_dvd, Nat.dvd_one] at h
    simp at h
    rw [h] at hp
    simp at hp
    exact hn
  --let g := XgcdType.start (a.toPNat a_pos) p
  --obtain ⟨f, h_f, v, c, d, e, r⟩ := gcd_props (a.toPNat a_pos) p
  refine remainder ?_


theorem order_dvd_prime_minus_one (hp : Nat.Prime p) : order a p ∣ p - 1 := by
  unfold order PrimitiveRoot at hg
  rw [Nat.findGreatest_eq_iff.2] at hg
  exact hg


theorem prime_primitive_root_count : #{g ∈ range n | g.PrimitiveRoot n} = p.totient - 1 := by
  sorry


theorem primitive_root_index_pow (hg : g.PrimitiveRoot n) : g ^ index a n g ≡ a [MOD n] := by
  unfold index
  unfold PrimitiveRoot order at hg
  --rw [Nat.findGreatest_eq_iff.2]
  rw [Nat.findGreatest_eq] at hg
  sorry




--example (p a b : Nat) (h₀ : Nat.Prime p) (h₁ : 0 < a ∧ a < p ∧ 0 < b ∧ b < p) (h2 : a + b ≡ 0 [MOD p]) : index := by
--  exact p.dvd_or_dvd h2
