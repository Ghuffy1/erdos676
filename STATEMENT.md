# Statement correspondence

## Original sources

- Paul Erdős, *Some unconventional problems in number theory*, Mathematics Magazine 52 (1979), no. 2, 67–70, page 68, problem 3. [Original scan](https://users.renyi.hu/~p_erdos/1979-22.pdf).
- [Erdős problem 676](https://www.erdosproblems.com/676).
- [JSP-000549](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000549). The rules snapshot used for preparation is awards commit `b1bfe454d37db2838ef76756830aeb23c40de95e`.

The original question asks whether every sufficiently large integer is a positive multiple of the square of a prime, plus a nonnegative integer remainder smaller than that prime. A complete negative answer settles this question.

| Original condition | Formal treatment |
| --- | --- |
| Every sufficiently large integer | `∀ᶠ n : ℕ in Filter.atTop`, the natural-number eventuality filter |
| Positive integer multiplier | `a : ℕ` and `1 ≤ a` |
| Prime base | `p : ℕ` and `p.Prime` |
| Nonnegative remainder, including zero | `b : ℕ`; the separate audit includes `0 ≤ b` explicitly |
| Remainder strictly smaller than the prime | `b < p` |
| Exact representation | `n = a * p ^ 2 + b` |
| A negative answer | `Erdos676.erdos676_negative` negates the entire eventual statement |
| Arbitrarily large exceptions | `JSP000549.arbitrarily_large_exceptions` and `Erdos676.full_unbounded_exceptions` |

The passage from integers to natural numbers preserves the question because every sufficiently large integer is nonnegative. The formal negation yields arbitrarily large natural-number exceptions.

## Endpoints and intermediate definitions

`representable_iff_mod` proves that a representation exists exactly when a prime `p` satisfies `p² ≤ n` and `n % p² < p`. This preserves the requirement that the multiplier is positive. Remainder zero is included throughout.

The proof estimates actual residue avoidance for small primes, then constructs centers whose entire averaging windows remain in `(X, 2X]` and avoid the eligible larger primes. Every prime that can represent a number in the window lies within the range checked by the final argument.

The mathematical paper proves both dyadic bounds. The formal quantitative target covers the lower bound, which already gives the complete negative answer to the JSP question. The paper's upper bound follows from its two-position sieve estimate at shift zero.

## Separate variants

The assertion obtained by allowing every integer base in place of prime `p`, and the questions about normalized remainders, are outside JSP-000549's stated prime-only target. The submission claims no resolution of those separate variants.

## Independent statement bridge

`audit/SubmissionAudit.lean` reconstructs the original assertion from natural-number arithmetic and the eventuality filter, with nonnegativity of the remainder explicit. It proves equivalence to the source definition and derives the negative answer. Its declarations, exact types, definitions and transitive axiom lists are printed during the default build and the explicit audit command.
