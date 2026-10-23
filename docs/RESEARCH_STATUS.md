# Current research obligations

Neither k=6 nor the unrestricted Erdős #677 is solved. This is the continuation state after the initial audit, not a solution claim or an award application.

The four-curve equivalence is complete and kernel-checked, including exact carry filters. Completing k=6 still requires showing that no branch has n>=0 and m>=n+6, or finding a genuine collision. The center gcd restrictions are bounded, but the centers themselves are not.

The most concrete global route currently has exact elliptic models, full Mordell–Weil bases reported by Magma, rational maps with denominator control, and an elliptic-logarithm upper bound. The missing obligations are rigorous height constants, logarithm intervals, an effective initial coefficient bound, LLL distance certificates, and an exhaustive final box justified by those bounds. See `cas/CAS.md`. This is a research program, not an executed completeness proof.

A separate uniform prime-power ownership route was checked. Write d=m-n. Every maximal prime power of the common LCM divides some d+j-i with 1<=i,j<=k, hence

`M_k(n) | lcm(d-k+1,...,d+k-1)`.

This is the paper's existing bridge restriction, not a new theorem. The universal valuation bound `P_k(n)/M_k(n) | (k-1)!` then gives only

`(n+1)^k <= (k-1)! (d+k-1)^(2k-1)`.

Along a fixed length-six product-ratio branch the positive real solution has d asymptotic to `((b/a)^(1/6)-1)n`. The inequality permits arbitrarily large scale; the loss from k factors to 2k-1 bridge slots prevents it from furnishing a global upper bound. Any improvement must retain additional information about which interval positions own each prime-power packet.

Finite congruence tests on the four product equations plus carry filters cannot alone complete this task: all four have positive disjoint representatives for every modulus, as proved in Lean. This does not rule out congruence methods combined with descent, certified bounds, or further arithmetic information.

If a full fixed-length proof is obtained, it will still not settle the original all-length conjecture. An admissible k=6 collision, however, would disprove it. Before any solution submission, the original intervals and exact LCMs, complete quantifiers, source competition and current upstream rules must be checked again.
