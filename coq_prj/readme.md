# Global Theorems and Their Importance

## 1. Core Global Theorems
### Upper Bound Theorems
- `superposition_bound`: Unifies the upper bound properties of three patterns.
- `combined_sequence_bound`: Provides a unified upper bound for any valid sequence.
- The importance of these theorems lies in their restriction of the growth range of sequences, providing a foundation for proving that sequences eventually converge.

## 2. Continuity Theorem Group
- `R0R1_continuity`
- `R1R0_continuity`
- `R0R0_continuity`
- This group of theorems proves the sustainability of operations, ensuring that sequences can continue indefinitely without producing illegal values. They are the cornerstone for constructing long sequence proofs.

## 3. Pattern Generation Theorem Group
- `valid_R0R1_entry_number_produces_d_R0R1`
- `valid_R1R0_entry_number_produces_d_R1R0`
- `valid_R0R0_entry_number_produces_d_R0`
- This group of theorems ensures that we can construct valid sequences of any length, providing tools for studying long-term behavior.

## 4. R0 Operation Dominance Properties (Proven)
- `R0_dominance_by_chains`: In any valid sequence, the number of R0 operations exceeds the number of R1 operations.
- `R0_dominance_by_ternary`: The count of R0 operations is at least double the count of R1 operations.
- `R0_count_grows_with_length`: As the sequence length increases, the advantage of R0 operations grows further.

## 5. Sequence Validity Preservation Properties (Proven)
- `sequence_validity_preservation`: The result of any valid sequence execution remains valid.
- `combined_pattern_continuity`: The result of combined pattern execution maintains validity.
- `R0R1_continuity`, `R1R0_continuity`, `R0R0_continuity`: Continuity of each basic pattern.

## 6. Pattern Comparison Properties (Proven)
- `pattern_value_comparison`: The size relationship between the three basic patterns (R0R1, R1R0, R0R0).
- `R0R0_special_properties`: Special properties of the R0R0 pattern (always produces multiples of powers of 2).
- `R0R0_monotonicity`: The monotonicity of the R0R0 pattern.

## 7. Sequence Decomposition Properties (Proven)
- `collatz_sequence_composition`: Sequences can be decomposed into binary combinations.
- `collatz_ternary_composition`: Sequences can be decomposed into ternary combinations.
- `binary_combination_completeness`: Completeness of binary combinations.
- `ternary_combination_completeness`: Completeness of ternary combinations.

## 8. Growth Rate Properties (Proven)
- `R0R1_growth_rate`: The growth rate of the R0R1 pattern.
- `R1R0_growth_rate`: The growth rate of the R1R0 pattern.
- `R0R0_growth_rate`: The growth rate of the R0R0 pattern.

## 9. Manifestation of Globality
### Universal Applicability
- Applies to all valid inputs.
- Not dependent on specific numerical values.
- Conclusions can be used in any combination.

### Constructiveness
- Can be used to build more complex proofs.
- Provides clear methods for sequence construction.
- Gives specific boundary values.

### Combinability
- Theorems can be combined with each other.
- Supports the proof of more complex properties.
- Forms a complete theoretical framework.

## 10. Current Main Convergence Proof
- `R0_count_grows_with_length`: As the sequence length increases, the advantage of R0 operations grows further, marking a significant achievement in our convergence proof. It proves that as the sequence gets longer, the number of X/2 operations in the sequence increases, starting from at least twice the number of R1 operations (3n+1 operations).

## 11. Numerical Sequence
### Sequence Descent Properties (Ongoing Proof)
- `sequence_descent`: For any valid input greater than 1, there exists an operation sequence that decreases the value.
- `value_descent`: When the number of R0 operations is sufficiently greater than the number of R1 operations, the sequence value will decrease.
- `sequence_descent` serves as the core theorem, directly supporting the argument that sequences will eventually converge to 1.
