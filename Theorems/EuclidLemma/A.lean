import Mathlib

/-!
# Euclid's lemma — Formalizer A statement

Source (Wikipedia, "Euclid's lemma", lead; Euclid, *Elements* VII.30):
> If a prime p divides the product ab of two integers a and b, then p must divide
> at least one of those integers a or b.
-/

namespace TuriMath.EuclidLemma.A

/-- Euclid's lemma.

Mapping from the source quote to the Lean:
* "a prime p"              → `p : ℕ` with `Nat.Prime p` (Mathlib's prime predicate on ℕ:
                              p = 2, 3, 5, …; ℕ not ℤ because "a prime" is a prime number).
* "two integers a and b"   → `a b : ℤ`, unrestricted (negative and zero allowed).
* "the product ab"         → `a * b` in ℤ.
* "p divides …"            → `(p : ℤ) ∣ …`, divisibility in ℤ (p cast to ℤ).
* "If …, then …"           → implication `→`, universally quantified over p, a, b.
* "at least one of a or b" → inclusive `∨`: `(p : ℤ) ∣ a ∨ (p : ℤ) ∣ b`.
-/
def Statement : Prop :=
  ∀ (p : ℕ), Nat.Prime p → ∀ (a b : ℤ), (p : ℤ) ∣ a * b → (p : ℤ) ∣ a ∨ (p : ℤ) ∣ b

/-! ## Sanity section
The hypotheses are `Nat.Prime p` and `(p : ℤ) ∣ a * b`. They can hold at once:
p = 2, a = 3, b = -4 (so ab = -12). -/

example : Nat.Prime 2 ∧ ((2 : ℕ) : ℤ) ∣ (3 : ℤ) * (-4) :=
  ⟨Nat.prime_two, ⟨-6, by norm_num⟩⟩

/-- A second instance with a zero factor: p = 5, a = 0, b = 7. -/
example : Nat.Prime 5 ∧ ((5 : ℕ) : ℤ) ∣ (0 : ℤ) * 7 :=
  ⟨by norm_num, ⟨0, by norm_num⟩⟩

end TuriMath.EuclidLemma.A
