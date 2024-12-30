import Mathlib
import Paperproof

open Nat

example (n : Nat) : (3 * n).totient = 3 * n.totient ↔ n ≡ 0 [MOD 3] := by
  constructor
  . intro h
    apply modEq_zero_iff_dvd.2
    by_contra h2
    conv_lhs at h =>
      apply totient_mul
      tactic =>
        apply Nat.coprime_of_dvd
        intro k h_k h_kn
        rw [Nat.dvd_prime] at h_kn
        rcases h_kn with (h_kl | h_kr)
        . exfalso
          rw [h_kl] at h_k
          exact Nat.not_prime_one h_k
        . simp [← h_kr] at h2
          exact h2
        decide
      done
    have : totient 3 = 2 := by decide
    conv_lhs at h =>
      enter [1]
      rw [this]
    simp at h
    subst h
    contradiction
  . intro h
    refine totient_mul_of_prime_of_dvd ?_ ?_
    . decide
    . exact dvd_of_mod_eq_zero h
